extern crate jni;
extern crate viper_sys;

use jni::JNIEnv;
use jni::objects::JObject;
use ast_factory::*;
use viper_sys::wrappers::viper::*;
use jni_utils::JniUtils;
use verification_result::VerificationResult;
use verification_result::VerificationError;
use ast_utils::AstUtils;
use std::marker::PhantomData;

pub mod state {
    pub enum Uninitialized {}
    pub enum Stopped {}
    pub enum Started {}
}

pub struct Verifier<'a, VerifierState> {
    env: &'a JNIEnv<'a>,
    silicon_wrapper: silicon::Silicon<'a>,
    silicon_instance: JObject<'a>,
    jni: JniUtils<'a>,
    state: PhantomData<VerifierState>,
}

impl<'a, VerifierState> Verifier<'a, VerifierState> {
    pub fn new(env: &'a JNIEnv) -> Verifier<'a, state::Uninitialized> {
        let jni = JniUtils::new(env);
        let silicon_wrapper = silicon::Silicon::with(env);
        let silicon_instance = jni.unwrap_result(silicon_wrapper.new());

        Verifier {
            env,
            silicon_wrapper,
            silicon_instance,
            jni,
            state: PhantomData,
        }
    }
}

impl<'a> Verifier<'a, state::Uninitialized> {
    pub fn parse_command_line(self, args: Vec<&str>) -> Verifier<'a, state::Stopped> {
        {
            let args = self.jni
                .new_seq(args.iter().map(|x| self.jni.new_string(x)).collect());
            self.jni.unwrap_result(
                self.silicon_wrapper
                    .call_parseCommandLine(self.silicon_instance, args),
            );
        }
        Verifier {
            env: self.env,
            silicon_wrapper: self.silicon_wrapper,
            silicon_instance: self.silicon_instance,
            jni: self.jni,
            state: PhantomData,
        }
    }
}

impl<'a> Verifier<'a, state::Stopped> {
    pub fn start(self) -> Verifier<'a, state::Started> {
        self.jni
            .unwrap_result(self.silicon_wrapper.call_start(self.silicon_instance));

        Verifier {
            env: self.env,
            silicon_wrapper: self.silicon_wrapper,
            silicon_instance: self.silicon_instance,
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

        let consistency_errors = ast_utils.check_consistency(program);

        if !consistency_errors.is_empty() {
            error!(
                "The provided program has {} consistency errors.",
                consistency_errors.len()
            );
            for error in consistency_errors {
                error!("{}", self.jni.to_string(error));
            }
            panic!();
        }

        let viper_result = self.jni.unwrap_result(
            self.silicon_wrapper
                .call_verify(self.silicon_instance, program.to_jobject()),
        );

        debug!(
            "Viper verification result: {}",
            self.jni.to_string(viper_result)
        );

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

                let error_type = self.jni.get_string(
                    self.jni
                        .unwrap_result(verification_error_wrapper.call_id(viper_error)),
                );

                let pos = self.jni
                    .unwrap_result(verification_error_wrapper.call_pos(viper_error));

                assert!(
                    self.jni
                        .is_instance_of(pos, "viper/silver/ast/HasIdentifier",),
                    format!(
                        "The verifier returned an error whose position has no identifier: {:?}",
                        self.jni.to_string(viper_error)
                    )
                );

                let pos_id = self.jni
                    .get_string(self.jni.unwrap_result(has_identifier_wrapper.call_id(pos)));

                errors.push(VerificationError::new(error_type, pos_id))
            }

            VerificationResult::Failure(errors)
        } else {
            VerificationResult::Success()
        }
    }
}
