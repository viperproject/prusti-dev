// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    ast_factory::*,
    ast_utils::AstUtils,
    jni_utils::JniUtils,
    silicon_counterexample::SiliconCounterexample,
    smt_manager::SmtManager,
    verification_backend::VerificationBackend,
    verification_result::{VerificationError, VerificationResult}, ConsistencyError,
};
use jni::{errors::Result, objects::JObject, JNIEnv};
use log::{debug, error, info};
use std::path::PathBuf;
use viper_sys::wrappers::{scala, viper::*};

pub struct Verifier<'a> {
    env: &'a JNIEnv<'a>,
    verifier_wrapper: silver::verifier::Verifier<'a>,
    verifier_instance: JObject<'a>,
    frontend_wrapper: silver::frontend::SilFrontend<'a>,
    frontend_instance: JObject<'a>,
    jni: JniUtils<'a>,
    ast_utils: AstUtils<'a>,
    smt_manager: SmtManager,
}

impl<'a> Verifier<'a> {
    pub fn new(
        env: &'a JNIEnv,
        backend: VerificationBackend,
        report_path: Option<PathBuf>,
        smt_manager: SmtManager,
    ) -> Self {
        let jni = JniUtils::new(env);
        let ast_utils = AstUtils::new(env);
        let verifier_wrapper = silver::verifier::Verifier::with(env);
        let frontend_wrapper = silver::frontend::SilFrontend::with(env);

        let frontend_instance = jni.unwrap_result(env.with_local_frame(16, || {
            let reporter = if let Some(real_report_path) = report_path {
                jni.unwrap_result(silver::reporter::CSVReporter::with(env).new(
                    jni.new_string("csv_reporter"),
                    jni.new_string(real_report_path.to_str().unwrap()),
                ))
            } else {
                jni.unwrap_result(silver::reporter::NoopReporter_object::with(env).singleton())
            };

            let debug_info = jni.new_seq(&[]);

            let backend_unwrapped = Self::instantiate_verifier(backend, env, reporter, debug_info);
            let backend_instance = jni.unwrap_result(backend_unwrapped);

            let logger_singleton =
                jni.unwrap_result(silver::logger::SilentLogger_object::with(env).singleton());
            let logger_factory = jni.unwrap_result(
                silver::logger::SilentLogger_object::with(env).call_apply(logger_singleton),
            );
            let logger =
                jni.unwrap_result(silver::logger::ViperLogger::with(env).call_get(logger_factory));

            let unwrapped_frontend_instance = {
                match backend {
                    VerificationBackend::Silicon => {
                        silicon::SiliconFrontend::with(env).new(reporter, logger)
                    }
                    VerificationBackend::Carbon => {
                        carbon::CarbonFrontend::with(env).new(reporter, logger)
                    }
                }
            };
            let frontend_instance = jni.unwrap_result(unwrapped_frontend_instance);

            frontend_wrapper
                .call_setVerifier(frontend_instance, backend_instance)
                .unwrap();
            let verifier_option = jni.new_option(Some(backend_instance));

            frontend_wrapper
                .set___verifier(frontend_instance, verifier_option)
                .unwrap();

            Ok(frontend_instance)
        }));

        let verifier_instance = jni.unwrap_result(env.with_local_frame(16, || {
            let verifier_instance =
                jni.unwrap_result(frontend_wrapper.call_verifier(frontend_instance));

            let consistency_check_state = silver::frontend::DefaultStates::with(env)
                .call_ConsistencyCheck()
                .unwrap();

            frontend_wrapper
                .call_setState(frontend_instance, consistency_check_state)
                .unwrap();

            let name =
                jni.to_string(jni.unwrap_result(verifier_wrapper.call_name(verifier_instance)));
            let build_version = jni.to_string(
                jni.unwrap_result(verifier_wrapper.call_buildVersion(verifier_instance)),
            );
            info!("Using backend {} version {}", name, build_version);
            Ok(verifier_instance)
        }));

        Verifier {
            env,
            verifier_wrapper,
            verifier_instance,
            frontend_wrapper,
            frontend_instance,
            jni,
            ast_utils,
            smt_manager,
        }
    }

    #[tracing::instrument(level = "debug", skip_all)]
    fn instantiate_verifier(
        backend: VerificationBackend,
        env: &'a JNIEnv,
        reporter: JObject,
        debug_info: JObject,
    ) -> Result<JObject<'a>> {
        match backend {
            VerificationBackend::Silicon => silicon::Silicon::with(env).new(reporter, debug_info),
            VerificationBackend::Carbon => {
                carbon::CarbonVerifier::with(env).new(reporter, debug_info)
            }
        }
    }

    #[must_use]
    #[tracing::instrument(level = "debug", skip_all)]
    pub fn parse_command_line(self, args: &[String]) -> Self {
        self.ast_utils.with_local_frame(16, || {
            let args = self.jni.new_seq(
                &args
                    .iter()
                    .map(|x| self.jni.new_string(x))
                    .collect::<Vec<JObject>>(),
            );
            self.jni.unwrap_result(
                self.verifier_wrapper
                    .call_parseCommandLine(self.verifier_instance, args),
            );
        });
        self
    }

    #[must_use]
    #[tracing::instrument(level = "debug", skip_all)]
    pub fn start(self) -> Self {
        self.ast_utils.with_local_frame(16, || {
            self.jni
                .unwrap_result(self.verifier_wrapper.call_start(self.verifier_instance));
        });
        self
    }

    /// Extract a position identifier from a `Position` object.
    fn extract_pos_id(&self, pos: JObject<'_>) -> Option<String> {
        let has_identifier_wrapper = silver::ast::HasIdentifier::with(self.env);

        if self
            .jni
            .is_instance_of(pos, "viper/silver/ast/HasIdentifier")
        {
            Some(
                self.jni.get_string(
                    self.jni
                        .unwrap_result(has_identifier_wrapper.call_id(pos)),
                ),
            )
        } else {
            None
        }
    }

    #[tracing::instrument(name = "viper::verify", level = "debug", skip_all)]
    pub fn verify(&mut self, program: Program) -> VerificationResult {
        let ast_utils = self.ast_utils;
        ast_utils.with_local_frame(16, || {
            debug!(
                "Program to be verified:\n{}",
                self.ast_utils.pretty_print(program)
            );

            run_timed!("Viper consistency checks", debug,
                let consistency_errors = match self.ast_utils.check_consistency(program) {
                    Ok(errors) => errors,
                    Err(java_exception) => {
                        return VerificationResult::JavaException(java_exception);
                    }
                };
            );

            if !consistency_errors.is_empty() {

                let consistency_error_wrapper = silver::verifier::ConsistencyError::with(self.env);

                debug!(
                    "The provided Viper program has {} consistency errors.",
                    consistency_errors.len()
                );
                return VerificationResult::ConsistencyErrors(
                    consistency_errors
                        .into_iter()
                        .map(|e| {
                            let pos = self
                                .jni
                                .unwrap_result(consistency_error_wrapper.call_pos(e));

                            let pos_id = self.extract_pos_id(pos);

                            let message =
                                self.jni.to_string(self.jni.unwrap_result(
                                    consistency_error_wrapper.call_readableMessage(e),
                                ));
                            ConsistencyError { pos_id, message }
                        })
                        .collect(),
                );
            }

            let program_option = self.jni.new_option(Some(program.to_jobject()));
            self.jni.unwrap_result(self.frontend_wrapper.set___program(self.frontend_instance, program_option));

            run_timed!("Viper verification", debug,
                self.jni.unwrap_result(self.frontend_wrapper.call_verification(self.frontend_instance));
                let viper_result_option = self.jni.unwrap_result(self.frontend_wrapper.call_getVerificationResult(self.frontend_instance));
                let viper_result = self.jni.unwrap_result(scala::Some::with(self.env).call_get(viper_result_option));
            );
            debug!(
                "Viper verification result: {}",
                self.jni.to_string(viper_result)
            );

            let is_failure = self
                .jni
                .is_instance_of(viper_result, "viper/silver/verifier/Failure");

            self.smt_manager.stop_and_check();

            if is_failure {
                let mut errors: Vec<VerificationError> = vec![];

                let viper_errors = self.jni.seq_to_vec(self.jni.unwrap_result(
                    silver::verifier::Failure::with(self.env).call_errors(viper_result),
                ));


                let verification_error_wrapper = silver::verifier::VerificationError::with(self.env);

                let error_node_positioned_wrapper = silver::ast::Positioned::with(self.env);

                let failure_context_wrapper = silver::verifier::FailureContext::with(self.env);

                let error_reason_wrapper = silver::verifier::ErrorReason::with(self.env);

                for viper_error in viper_errors {
                    let is_verification_error = self
                        .jni
                        .is_instance_of(viper_error, "viper/silver/verifier/VerificationError");

                    if !is_verification_error {
                        let is_aborted_exceptionally = self
                            .jni
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
                        unreachable!(
                            "The verifier returned an unknown error of type {}: {}",
                            self.jni.class_name(viper_error),
                            self.jni.to_string(viper_error)
                        );
                    };
                    let mut failure_contexts = self.jni.seq_to_vec(self
                    .jni
                    .unwrap_result(verification_error_wrapper.call_failureContexts(viper_error)));

                    let counterexample: Option<SiliconCounterexample> = {
                        if let Some(failure_context) = failure_contexts.pop() {
                            let option_original_counterexample = self
                                .jni
                                .unwrap_result(failure_context_wrapper.call_counterExample(failure_context));
                            if !self
                                .jni
                                .is_instance_of(option_original_counterexample, "scala/None$")
                            {
                                let original_counterexample = self.jni.unwrap_result(
                                    scala::Some::with(self.env).call_get(option_original_counterexample),
                                );
                                if self.jni.is_instance_of(
                                    original_counterexample,
                                    "viper/silicon/interfaces/SiliconMappedCounterexample",
                                ) {
                                    // only mapped counterexamples are processed
                                    Some(SiliconCounterexample::new(
                                        self.env,
                                        self.jni,
                                        original_counterexample,
                                    ))
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    };

                    let reason = self
                        .jni
                        .unwrap_result(verification_error_wrapper.call_reason(viper_error));

                    let reason_pos = self
                        .jni
                        .unwrap_result(error_reason_wrapper.call_pos(reason));

                    let reason_pos_id = self.extract_pos_id(reason_pos);
                    if reason_pos_id.is_none() {
                        debug!(
                            "The verifier returned an error whose offending node position has no identifier: {:?}",
                            self.jni.to_string(viper_error)
                        );
                    }

                    let error_full_id = self.jni.get_string(
                        self.jni
                            .unwrap_result(verification_error_wrapper.call_fullId(viper_error)),
                    );

                    let pos = self
                        .jni
                        .unwrap_result(verification_error_wrapper.call_pos(viper_error));

                    let message =
                        self.jni.to_string(self.jni.unwrap_result(
                            verification_error_wrapper.call_readableMessage(viper_error),
                        ));

                    let pos_id = self.extract_pos_id(pos);
                    if pos_id.is_none() {
                        debug!(
                            "The verifier returned an error whose position has no identifier: {:?}",
                            self.jni.to_string(viper_error)
                        );
                    }

                    let offending_node = self
                        .jni
                        .unwrap_result(verification_error_wrapper.call_offendingNode(viper_error));

                    let offending_pos = self
                        .jni
                        .unwrap_result(error_node_positioned_wrapper.call_pos(offending_node));

                    let offending_pos_id = self.extract_pos_id(offending_pos);
                    if offending_pos_id.is_none() {
                        debug!(
                            "The verifier returned an error whose offending node position has no identifier: {:?}",
                            self.jni.to_string(viper_error)
                        );
                    }

                    errors.push(VerificationError::new(
                        error_full_id,
                        pos_id,
                        offending_pos_id,
                        reason_pos_id,
                        message,
                        counterexample,
                    ))
                }

                VerificationResult::Failure(errors)
            } else {
                VerificationResult::Success
            }
        })
    }
}

impl<'a> Drop for Verifier<'a> {
    fn drop(&mut self) {
        // Tell the verifier to stop its threads.
        self.jni
            .unwrap_result(self.verifier_wrapper.call_stop(self.verifier_instance));
        // Delete the local reference to the verifier in the JVM
        // so that the JVM garbage collector can clean it up.
        self.jni
            .unwrap_result(self.env.delete_local_ref(self.verifier_instance));
        self.jni
            .unwrap_result(self.env.delete_local_ref(self.frontend_instance));
    }
}
