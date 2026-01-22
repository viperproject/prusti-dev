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
    verification_result::{VerificationError, VerificationResultKind},
    ConsistencyError,
};
use jni::{errors::Result, objects::JObject, JNIEnv};
use log::{debug, error, info};
use std::{
    collections::{hash_map::DefaultHasher, HashSet},
    hash::{Hash, Hasher},
    marker::PhantomData,
    path::PathBuf,
    thread::ScopedJoinHandle,
};
use viper_sys::wrappers::{scala, viper::*};

mod lifetime_state {
    /// The JVM object for the underlying verifier has been created, but not yet configured.
    pub(crate) struct Instantiated;

    /// The verifier has been configured, and verification has started on a
    /// Viper program.
    pub struct Started;
}

use lifetime_state::*;

/// Implementations of this trait correspond to the different states of the
/// underlying Viper verifier. See [`lifetime_state::Instantiated`] and
/// [`lifetime_state::Started`].
pub(crate) trait LifetimeState {
    /// Silicon tracks the lifetime state of the verifier explicitly via a value
    /// of a Scala enumeration type.  Implementations of LifetimeState should
    /// provide the class name of the corresponding Scala enumeration value that
    /// would be used in Silicon: if Silicon is used, then Prusti will verify
    /// that the Silicon's enumeration value is consistent with the tracked
    /// state in the [`Verifier`] object (see [`Verifier::assert_verifier_state_and_invariants`]).
    const SILICON_JAVA_CLASSNAME: &'static str;

    /// Asserts properties that should hold when the verifier is in this state.
    fn assert_state_invariants<'a>(
        _jni_utils: &JniUtils<'a>,
        _frontend_wrapper: &silver::frontend::SilFrontend<'a>,
        _frontend_instance: JObject<'a>,
    ) {
    }
}

impl LifetimeState for Instantiated {
    const SILICON_JAVA_CLASSNAME: &'static str =
        "viper.silicon.Silicon$LifetimeState$Instantiated$";
}

impl LifetimeState for Started {
    const SILICON_JAVA_CLASSNAME: &'static str = "viper.silicon.Silicon$LifetimeState$Started$";

    fn assert_state_invariants<'a>(
        jni_utils: &JniUtils<'a>,
        frontend_wrapper: &silver::frontend::SilFrontend<'a>,
        frontend_instance: JObject<'a>,
    ) {
        let config = jni_utils.unwrap_result(frontend_wrapper.call_config(frontend_instance));
        assert!(!config.is_null(), "config is null");
    }
}

pub(crate) trait TransitionsTo<Next: LifetimeState> {}

impl TransitionsTo<Started> for Instantiated {}

pub struct Verifier<'a, State = Started> {
    env: &'a JNIEnv<'a>,
    backend: VerificationBackend,
    verifier_wrapper: silver::verifier::Verifier<'a>,
    verifier_instance: JObject<'a>,
    frontend_wrapper: silver::frontend::SilFrontend<'a>,
    frontend_instance: JObject<'a>,
    jni: JniUtils<'a>,
    ast_utils: AstUtils<'a>,
    smt_manager: SmtManager,
    _marker: PhantomData<State>,
}

impl<'a, State> Verifier<'a, State> {
    /// Asserts that the underlying Viper verifier is an a state that is
    /// consistent with `ExpectedState` (this does not take the current state into account).
    fn assert_verifier_state_and_invariants<ExpectedState: LifetimeState>(&self) {
        if let VerificationBackend::Silicon = self.backend {
            let wrapper = silicon::Silicon::with(self.env);
            let jni_state = self
                .jni
                .unwrap_result(wrapper.get_lifetimeState(self.verifier_instance));
            assert_eq!(
                self.jni.class_name(jni_state),
                ExpectedState::SILICON_JAVA_CLASSNAME,
            );
            ExpectedState::assert_state_invariants(
                &self.jni,
                &self.frontend_wrapper,
                self.frontend_instance,
            );
        }
    }

    /// Asserts that the underlying Viper verifier is in a state that is
    /// consistent with the current state of the [`Verifier`] object.
    fn assert_lifetime_state_consistency(&self)
    where
        State: LifetimeState,
    {
        self.assert_verifier_state_and_invariants::<State>();
    }

    /// Verifies that the underlying Viper verifier state corresponds to to
    /// `Next`, and returns an instance of [`Verifier`] representing that the
    /// underlying Viper verifier is in that state.
    fn transition_state_to<Next: LifetimeState>(self) -> Verifier<'a, Next>
    where
        State: TransitionsTo<Next>,
    {
        self.assert_verifier_state_and_invariants::<Next>();
        // SAFETY: Only ghost state changes
        unsafe { std::mem::transmute(self) }
    }
}

impl<'a> Verifier<'a, Instantiated> {
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
            let pass_through_reporter = if let Some(real_report_path) = report_path {
                jni.unwrap_result(silver::reporter::CSVReporter::with(env).new(
                    jni.new_string("csv_reporter"),
                    jni.new_string(real_report_path.to_str().unwrap()),
                ))
            } else {
                jni.unwrap_result(silver::reporter::NoopReporter_object::with(env).singleton())
            };

            let reporter = jni.unwrap_result(
                silver::reporter::PollingReporter::with(env)
                    .new(jni.new_string("polling_reporter"), pass_through_reporter),
            );

            let debug_info = jni.new_seq(&[]);

            let backend_unwrapped = Self::instantiate_verifier(backend, env, reporter, debug_info);
            let backend_instance = jni.unwrap_result(backend_unwrapped);
            assert!(!backend_instance.is_null(), "backend_instance is null");

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

            frontend_wrapper
                .call_init(frontend_instance, backend_instance)
                .unwrap();

            Ok(frontend_instance)
        }));

        let verifier_instance = jni.unwrap_result(env.with_local_frame(16, || {
            let verifier_instance =
                jni.unwrap_result(frontend_wrapper.call_verifier(frontend_instance));

            assert!(!verifier_instance.is_null(), "verifier_instance is null");

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
            info!("Using backend {name} version {build_version}");
            Ok(verifier_instance)
        }));

        let verifier = Verifier {
            env,
            verifier_wrapper,
            verifier_instance,
            frontend_wrapper,
            frontend_instance,
            jni,
            ast_utils,
            smt_manager,
            backend,
            _marker: PhantomData,
        };
        verifier.assert_lifetime_state_consistency();
        verifier
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
    pub fn parse_command_line(self, args: &[String]) -> Verifier<'a, Started> {
        self.ast_utils.with_local_frame(16, || {
            let args = self.jni.new_seq(
                &args
                    .iter()
                    .map(|x| self.jni.new_string(x))
                    .collect::<Vec<JObject>>(),
            );
            self.jni.unwrap_result(
                self.frontend_wrapper
                    .call_parseCommandLine(self.frontend_instance, args),
            );
        });
        self.transition_state_to::<Started>()
    }
}

impl<'a> Verifier<'a> {
    #[tracing::instrument(name = "viper::verify", level = "debug", skip_all)]
    pub fn verify(
        &mut self,
        program: Program,
        polling_thread: Option<ScopedJoinHandle<HashSet<u64>>>,
    ) -> VerificationResultKind {
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
                        return VerificationResultKind::JavaException(java_exception);
                    }
                };
            );

            if !consistency_errors.is_empty() {

                let consistency_error_wrapper = silver::verifier::ConsistencyError::with(self.env);

                debug!(
                    "The provided Viper program has {} consistency errors.",
                    consistency_errors.len()
                );
                return VerificationResultKind::ConsistencyErrors(
                    consistency_errors
                        .into_iter()
                        .map(|e| {
                            let pos = self
                                .jni
                                .unwrap_result(consistency_error_wrapper.call_pos(e));

                            let pos_id = extract_pos_id(&self.jni, self.env, pos);

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

            self.assert_lifetime_state_consistency();
            run_timed!("Viper verification", debug,
                self.jni.unwrap_result(self.frontend_wrapper.call_verification(self.frontend_instance));
                let viper_result_option = self.jni.unwrap_result(self.frontend_wrapper.call_getVerificationResult(self.frontend_instance));
            );
            let is_empty = self.jni.unwrap_result(scala::Option::with(self.env).call_isEmpty(viper_result_option));
            if is_empty {
                panic!("Error during typechecking/consistency checking!");
            }
            let viper_result = self.jni.unwrap_result(scala::Some::with(self.env).call_get(viper_result_option));
            debug!(
                "Viper verification result: {}",
                self.jni.to_string(viper_result)
            );

            let is_failure = self
                .jni
                .is_instance_of(viper_result, "viper/silver/verifier/Failure");

            self.smt_manager.stop_and_check();

            // wait for the polling thread if present so no errors get processed here that should
            // be processed by the polling thread. Also avoids the need for locking.
            let error_hashes_opt = polling_thread.map(|pt| pt.join().unwrap());
            if is_failure {
                if let Some(mut error_hashes) = error_hashes_opt {
                    debug!("processing final errors. already did {error_hashes:?}");
                    extract_errors(&self.jni, self.env, viper_result, Some(&mut error_hashes))
                } else {
                    extract_errors(&self.jni, self.env, viper_result, None)
                }
            } else {
                VerificationResultKind::Success
            }
        })
    }
}

impl<'a, State> Verifier<'a, State> {
    pub fn verifier_instance(&self) -> &JObject<'a> {
        &self.verifier_instance
    }
}

impl<State> Drop for Verifier<'_, State> {
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

/// Extract a position identifier from a `Position` object.
fn extract_pos_id(jni_utils: &JniUtils<'_>, env: &JNIEnv<'_>, pos: JObject<'_>) -> Option<String> {
    let has_identifier_wrapper = silver::ast::HasIdentifier::with(env);

    if jni_utils.is_instance_of(pos, "viper/silver/ast/HasIdentifier") {
        Some(jni_utils.get_string(jni_utils.unwrap_result(has_identifier_wrapper.call_id(pos))))
    } else {
        None
    }
}

pub fn extract_errors(
    jni_utils: &JniUtils<'_>,
    env: &JNIEnv<'_>,
    viper_result: JObject<'_>, // viper::silicon::verification::Failure
    mut error_hashes_opt: Option<&mut HashSet<u64>>,
) -> VerificationResultKind {
    let mut errors: Vec<VerificationError> = vec![];

    let viper_errors = jni_utils.seq_to_vec(
        jni_utils.unwrap_result(silver::verifier::Failure::with(env).call_errors(viper_result)),
    );

    let verification_error_wrapper = silver::verifier::VerificationError::with(env);
    let error_node_positioned_wrapper = silver::ast::Positioned::with(env);
    let failure_context_wrapper = silver::verifier::FailureContext::with(env);
    let error_reason_wrapper = silver::verifier::ErrorReason::with(env);

    for viper_error in viper_errors {
        let is_verification_error =
            jni_utils.is_instance_of(viper_error, "viper/silver/verifier/VerificationError");

        if !is_verification_error {
            let is_aborted_exceptionally =
                jni_utils.is_instance_of(viper_error, "viper/silver/verifier/AbortedExceptionally");

            if is_aborted_exceptionally {
                let exception = jni_utils.unwrap_result(
                    silver::verifier::AbortedExceptionally::with(env).call_cause(viper_error),
                );
                let stack_trace = jni_utils.unwrap_result(jni_utils.get_stack_trace(exception));
                error!("The verification aborted due to the following exception: {stack_trace}");
            } else {
                error!(
                    "The verifier returned an unhandled error of type {}: {}",
                    jni_utils.class_name(viper_error),
                    jni_utils.to_string(viper_error)
                );
            }
            unreachable!(
                "The verifier returned an unknown error of type {}: {}",
                jni_utils.class_name(viper_error),
                jni_utils.to_string(viper_error)
            );
        };

        let reason = jni_utils.unwrap_result(verification_error_wrapper.call_reason(viper_error));

        let reason_pos = jni_utils.unwrap_result(error_reason_wrapper.call_pos(reason));

        let reason_pos_id = extract_pos_id(jni_utils, env, reason_pos);
        if reason_pos_id.is_none() {
            debug!(
                "The verifier returned an error whose reason position has no identifier: {:?}",
                jni_utils.to_string(viper_error)
            );
        }

        let error_full_id = jni_utils.get_string(
            jni_utils.unwrap_result(verification_error_wrapper.call_fullId(viper_error)),
        );

        let pos = jni_utils.unwrap_result(verification_error_wrapper.call_pos(viper_error));

        let pos_id = extract_pos_id(jni_utils, env, pos);
        if pos_id.is_none() {
            debug!(
                "The verifier returned an error whose position has no identifier: {:?}",
                jni_utils.to_string(viper_error)
            );
        }

        let offending_node =
            jni_utils.unwrap_result(verification_error_wrapper.call_offendingNode(viper_error));

        let offending_pos =
            jni_utils.unwrap_result(error_node_positioned_wrapper.call_pos(offending_node));

        let offending_pos_id = extract_pos_id(jni_utils, env, offending_pos);
        if offending_pos_id.is_none() {
            debug!(
                "The verifier returned an error whose offending node position has no identifier: {:?}",
                jni_utils.to_string(viper_error)
            );
        }

        // We only process errors that have not been processed yet. This mainly skips errors
        // that occurred during the verification of user-written rust functions. Any other errors
        // will still be processed here by the verifier for the overall result.
        if let Some(ref mut error_hashes) = error_hashes_opt {
            let error_hash = hash_error(&error_full_id, &pos_id, &offending_pos_id, &reason_pos_id);
            if (error_hashes).contains(&error_hash) {
                debug!("already processed {error_hash}");
                continue;
            }
            debug!("processing {error_hash}");
            (error_hashes).insert(error_hash);
        }

        let message = jni_utils.to_string(
            jni_utils.unwrap_result(verification_error_wrapper.call_readableMessage(viper_error)),
        );

        let mut failure_contexts = jni_utils.seq_to_vec(
            jni_utils.unwrap_result(verification_error_wrapper.call_failureContexts(viper_error)),
        );

        let counterexample: Option<SiliconCounterexample> = {
            if let Some(failure_context) = failure_contexts.pop() {
                let option_original_counterexample = jni_utils
                    .unwrap_result(failure_context_wrapper.call_counterExample(failure_context));
                if !jni_utils.is_instance_of(option_original_counterexample, "scala/None$") {
                    let original_counterexample = jni_utils.unwrap_result(
                        scala::Some::with(env).call_get(option_original_counterexample),
                    );
                    if jni_utils.is_instance_of(
                        original_counterexample,
                        "viper/silicon/interfaces/SiliconMappedCounterexample",
                    ) {
                        // only mapped counterexamples are processed
                        Some(SiliconCounterexample::new(
                            env,
                            *jni_utils,
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

        errors.push(VerificationError::new(
            error_full_id,
            pos_id,
            offending_pos_id,
            reason_pos_id,
            message,
            counterexample,
        ))
    }

    VerificationResultKind::Failure(errors)
}

/// manually hash identifying parts of an error
fn hash_error(
    full_id: &str,
    pos_id: &Option<String>,
    offending_pos_id: &Option<String>,
    reason_pos_id: &Option<String>,
) -> u64 {
    let mut hasher = DefaultHasher::new();
    full_id.hash(&mut hasher);
    pos_id.hash(&mut hasher);
    offending_pos_id.hash(&mut hasher);
    reason_pos_id.hash(&mut hasher);
    hasher.finish()
}
