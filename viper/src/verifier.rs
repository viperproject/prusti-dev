// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![cfg_attr(feature = "cargo-clippy", allow(new_ret_no_self))]

use jni::JNIEnv;
use jni::objects::JObject;
use ast_factory::*;
use viper_sys::wrappers::viper::*;
use jni_utils::JniUtils;
use verification_result::VerificationResult;
use verification_result::VerificationError;
use verification_backend::VerificationBackend;
use ast_utils::AstUtils;
use std::marker::PhantomData;
use std::time::Instant;

pub mod state {
    pub struct Uninitialized;
    pub struct Stopped;
    pub struct Started;
}

pub struct Verifier<'a, VerifierState> {
    env: &'a JNIEnv<'a>,
    verifier_wrapper: silver::verifier::Verifier<'a>,
    verifier_instance: JObject<'a>,
    jni: JniUtils<'a>,
    state: PhantomData<VerifierState>,
}

impl<'a, VerifierState> Verifier<'a, VerifierState> {
    pub fn new(env: &'a JNIEnv, backend: VerificationBackend) -> Verifier<'a, state::Uninitialized> {
        let jni = JniUtils::new(env);
        let verifier_wrapper = silver::verifier::Verifier::with(env);
        let verifier_instance = jni.unwrap_result(match backend {
            VerificationBackend::Silicon => silicon::Silicon::with(env).new(),
            VerificationBackend::Carbon => carbon::CarbonVerifier::with(env).new(),
        });

        let name = jni.to_string(
            jni.unwrap_result(verifier_wrapper.call_name(verifier_instance))
        );
        let build_version = jni.to_string(
            jni.unwrap_result(verifier_wrapper.call_buildVersion(verifier_instance))
        );
        info!("Using backend {} version {}", name, build_version);

        Verifier {
            env,
            verifier_wrapper,
            verifier_instance,
            jni,
            state: PhantomData,
        }
    }
}

impl<'a> Verifier<'a, state::Uninitialized> {
    pub fn parse_command_line(self, args: &[&str]) -> Verifier<'a, state::Stopped> {
        {
            let args = self.jni.new_seq(&args.iter()
                .map(|x| self.jni.new_string(x))
                .collect::<Vec<JObject>>());
            self.jni.unwrap_result(
                self.verifier_wrapper
                    .call_parseCommandLine(self.verifier_instance, args),
            );
        }
        Verifier {
            env: self.env,
            verifier_wrapper: self.verifier_wrapper,
            verifier_instance: self.verifier_instance,
            jni: self.jni,
            state: PhantomData,
        }
    }
}

impl<'a> Verifier<'a, state::Stopped> {
    pub fn start(self) -> Verifier<'a, state::Started> {
        self.jni
            .unwrap_result(self.verifier_wrapper.call_start(self.verifier_instance));

        Verifier {
            env: self.env,
            verifier_wrapper: self.verifier_wrapper,
            verifier_instance: self.verifier_instance,
            jni: self.jni,
            state: PhantomData,
        }
    }
}

impl<'a> Verifier<'a, state::Started> {
    pub fn verify(&self, program: Program) -> VerificationResult {
        let ast_utils = AstUtils::new(self.env);

        debug!(
            "Program to be verified:\n{}",
            ast_utils.pretty_print(program)
        );

        let mut consistency_errors= vec![];

        // We suspect that there is a 1/1000 probability of getting false positive consistency
        // errors. So, we re-execute.
        for i in 0..5 {
            consistency_errors = ast_utils.check_consistency(program);
            if consistency_errors.is_empty() {
                if i != 0 {
                    debug!("Consistency errors disappeared after re-checking {} times.", i);
                }
                break;
            }
        }

        if !consistency_errors.is_empty() {
            error!(
                "The provided Viper program has {} consistency errors.",
                consistency_errors.len()
            );
            for error in consistency_errors {
                error!("{}", self.jni.to_string(error));
            }
            panic!("Consistency errors. The encoded Viper program is incorrect.");
        }

        let start_verification = Instant::now();
        let viper_result = self.jni.unwrap_result(
            self.verifier_wrapper
                .call_verify(self.verifier_instance, program.to_jobject())
        );
        let duration = start_verification.elapsed();

        debug!("Viper verification took {}.{} seconds", duration.as_secs(), duration.subsec_millis()/10);
        debug!("Viper verification result: {}", self.jni.to_string(viper_result));

        let is_failure = self.jni
            .is_instance_of(viper_result, "viper/silver/verifier/Failure");

        if is_failure {
            let mut errors: Vec<VerificationError> = vec![];

            let viper_errors = self.jni.seq_to_vec(self.jni.unwrap_result(
                silver::verifier::Failure::with(self.env).call_errors(viper_result),
            ));

            let verification_error_wrapper = silver::verifier::VerificationError::with(self.env);

            let has_identifier_wrapper = silver::ast::HasIdentifier::with(self.env);

            for viper_error in viper_errors {
                let is_verification_error = self.jni
                    .is_instance_of(viper_error, "viper/silver/verifier/VerificationError");

                if !is_verification_error {
                    let is_aborted_exceptionally = self.jni
                        .is_instance_of(viper_error, "viper/silver/verifier/AbortedExceptionally");

                    if is_aborted_exceptionally {
                        let exception = self.jni.unwrap_result(
                            silver::verifier::AbortedExceptionally::with(self.env)
                                .call_cause(viper_error),
                        );
                        let stack_trace =
                            self.jni.unwrap_result(self.jni.get_stack_trace(exception));
                        error!(
                            "The verification aborted due to the following exception: {}",
                            stack_trace
                        );
                    } else {
                        error!(
                            "The verifier returned an unhandled error of type {}: {}",
                            self.jni.class_name(viper_error),
                            self.jni.to_string(viper_error)
                        );
                    }
                    panic!();
                };

                let error_full_id = self.jni.get_string(
                    self.jni
                        .unwrap_result(verification_error_wrapper.call_fullId(viper_error)),
                );

                let pos = self.jni
                    .unwrap_result(verification_error_wrapper.call_pos(viper_error));

                let message = self.jni.to_string(
                    self.jni.unwrap_result(
                        verification_error_wrapper.call_readableMessage(viper_error)
                    )
                );

                let pos_id = if self.jni.is_instance_of(pos, "viper/silver/ast/HasIdentifier") {
                    Some(
                        self.jni.get_string(
                            self.jni.unwrap_result(has_identifier_wrapper.call_id(pos))
                        )
                    )
                } else {
                    debug!(
                        "The verifier returned an error whose position has no identifier: {:?}",
                        self.jni.to_string(viper_error)
                    );
                    None
                };

                errors.push(VerificationError::new(error_full_id, pos_id, message))
            }

            VerificationResult::Failure(errors)
        } else {
            VerificationResult::Success()
        }
    }
}
