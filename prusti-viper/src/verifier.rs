// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    counterexamples::{counterexample_translation, counterexample_translation_refactored},
    Encoder,
};
use ::log::{debug, error, info};
use once_cell::sync::Lazy;
use prusti_common::{
    config,
    report::log,
    vir::{optimizations::optimize_program, program::Program},
    Stopwatch,
};
use prusti_interface::{
    data::{VerificationResult, VerificationTask},
    environment::Environment,
    specs::typed,
    PrustiError,
};
use prusti_rustc_interface::span::DUMMY_SP;
use prusti_server::{
    process_verification_request, spawn_server_thread, tokio::runtime::Builder, PrustiClient,
    VerificationRequest, ViperBackendConfig,
};
use viper::{self, PersistentCache, Viper};
use vir_crate::common::check_mode::CheckMode;

/// A verifier is an object for verifying a single crate, potentially
/// many times.
pub struct Verifier<'v, 'tcx>
where
    'tcx: 'v,
{
    env: &'v Environment<'tcx>,
    encoder: Encoder<'v, 'tcx>,
}

impl<'v, 'tcx> Verifier<'v, 'tcx> {
    pub fn new(env: &'v Environment<'tcx>, def_spec: typed::DefSpecificationMap) -> Self {
        Verifier {
            env,
            encoder: Encoder::new(env, def_spec),
        }
    }

    #[tracing::instrument(name = "prusti_viper::verify", level = "info", skip(self))]
    pub fn verify(&mut self, task: &VerificationTask<'tcx>) -> VerificationResult {
        let mut stopwatch = Stopwatch::start("prusti-viper", "encoding to Viper");

        // Dump the configuration
        if config::dump_debug_info() {
            log::report("config", "prusti", config::dump());
        }

        for &proc_id in &task.procedures {
            let proc_name = self.env.name.get_absolute_item_name(proc_id);
            let proc_def_path = self.env.name.get_item_def_path(proc_id);
            let proc_span = self.env.query.get_def_span(proc_id);
            info!(" - {} ({})", proc_name, proc_def_path);
            info!("   Source: {:?}", proc_span);
        }
        for &proc_id in task.procedures.iter().rev() {
            // FIXME: Use the loop above.
            self.encoder.queue_procedure_encoding(proc_id);
        }
        for &type_id in task.types.iter().rev() {
            // FIXME: Use the loop above.
            self.encoder.queue_type_encoding(type_id);
        }
        self.encoder.process_encoding_queue();

        let encoding_errors_count = self.encoder.count_encoding_errors();

        let polymorphic_programs = self.encoder.get_viper_programs();

        let mut programs: Vec<Program> = if config::simplify_encoding() {
            stopwatch.start_next("optimizing Viper program");
            let source_file_name = self.encoder.env().name.source_file_name();
            polymorphic_programs
                .into_iter()
                .map(|program| Program::Legacy(optimize_program(program, &source_file_name).into()))
                .collect()
        } else {
            polymorphic_programs
                .into_iter()
                .map(|program| Program::Legacy(program.into()))
                .collect()
        };
        programs.extend(self.encoder.get_core_proof_programs());

        stopwatch.start_next("verifying Viper program");
        let verification_results = verify_programs(self.env, programs);
        stopwatch.finish();

        // Group verification results
        let mut verification_errors: Vec<_> = vec![];
        let mut consistency_errors: Vec<_> = vec![];
        let mut java_exceptions: Vec<_> = vec![];
        for (method_name, result) in verification_results.into_iter() {
            match result {
                backend_common::VerificationResult::Success => {}
                backend_common::VerificationResult::ConsistencyErrors(errors) => {
                    for error in errors.into_iter() {
                        consistency_errors.push((method_name.clone(), error));
                    }
                }
                backend_common::VerificationResult::Failure(errors) => {
                    for error in errors.into_iter() {
                        verification_errors.push((method_name.clone(), error));
                    }
                }
                backend_common::VerificationResult::JavaException(exception) => {
                    java_exceptions.push((method_name, exception));
                }
            }
        }

        // Convert verification results to Prusti errors
        let error_manager = self.encoder.error_manager();
        let mut result = VerificationResult::Success;

        for (method, error) in consistency_errors.into_iter() {
            PrustiError::internal(
                format!("consistency error in {method}: {error}"),
                DUMMY_SP.into(),
            )
            .emit(&self.env.diagnostic);
            result = VerificationResult::Failure;
        }

        for (method, exception) in java_exceptions.into_iter() {
            error!("Java exception: {}", exception.get_stack_trace());
            PrustiError::internal(format!("in {method}: {exception}"), DUMMY_SP.into())
                .emit(&self.env.diagnostic);
            result = VerificationResult::Failure;
        }

        // Report verification errors
        let mut prusti_errors: Vec<_> = vec![];
        for (method, verification_error) in verification_errors.into_iter() {
            debug!("Verification error in {}: {:?}", method, verification_error);
            let mut prusti_error = error_manager.translate_verification_error(&verification_error);

            // annotate with counterexample, if requested
            if config::counterexample() {
                if config::unsafe_core_proof() {
                    if let Some(silicon_counterexample) = &verification_error.counterexample {
                        if let Some(def_id) = error_manager.get_def_id(&verification_error) {
                            let counterexample =
                                counterexample_translation_refactored::backtranslate(
                                    &self.encoder,
                                    error_manager.position_manager(),
                                    def_id,
                                    silicon_counterexample,
                                );
                            prusti_error = counterexample.annotate_error(prusti_error);
                        } else {
                            prusti_error = prusti_error.add_note(
                                format!(
                                    "the verifier produced a counterexample for {method}, but it could not be mapped to source code"
                                ),
                                None,
                            );
                        }
                    }
                } else if let Some(silicon_counterexample) = &verification_error.counterexample {
                    if let Some(def_id) = error_manager.get_def_id(&verification_error) {
                        let counterexample = counterexample_translation::backtranslate(
                            &self.encoder,
                            def_id,
                            silicon_counterexample,
                        );
                        prusti_error = counterexample.annotate_error(prusti_error);
                    } else {
                        prusti_error = prusti_error.add_note(
                            format!(
                                "the verifier produced a counterexample for {method}, but it could not be mapped to source code"
                            ),
                            None,
                        );
                    }
                }
            }

            prusti_errors.push(prusti_error);
        }
        prusti_errors.sort();

        for prusti_error in prusti_errors {
            debug!("Prusti error: {:?}", prusti_error);
            if prusti_error.is_disabled() {
                prusti_error.cancel();
            } else {
                prusti_error.emit(&self.env.diagnostic);
            }
            result = VerificationResult::Failure;
        }

        if encoding_errors_count != 0 {
            result = VerificationResult::Failure;
        }

        result
    }
}

/// Verify a list of programs.
/// Returns a list of (program_name, verification_result) tuples.
fn verify_programs(env: &Environment, programs: Vec<Program>)
    -> Vec<(String, backend_common::VerificationResult)>
{
    let source_path = env.name.source_path();
    let rust_program_name = source_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned();
    let verification_requests = programs.into_iter().map(|mut program| {
        let program_name = program.get_name().to_string();
        let check_mode = program.get_check_mode();
        // Prepend the Rust file name to the program.
        program.set_name(format!("{rust_program_name}_{program_name}"));
        let backend = if check_mode == CheckMode::Specifications {
            config::verify_specifications_backend()
        } else {
            config::viper_backend()
        }
        .parse()
        .unwrap();
        let request = VerificationRequest {
            program,
            backend_config: ViperBackendConfig::new(backend),
        };
        (program_name, request)
    });
    if let Some(server_address) = config::server_address() {
        let server_address = if server_address == "MOCK" {
            spawn_server_thread().to_string()
        } else {
            server_address
        };
        info!("Connecting to Prusti server at {}", server_address);
        let client = PrustiClient::new(&server_address).unwrap_or_else(|error| {
            panic!("Could not parse server address ({server_address}) due to {error:?}")
        });
        // Here we construct a Tokio runtime to block until completion of the futures returned by
        // `client.verify`. However, to report verification errors as early as possible,
        // `verify_programs` should return an asynchronous stream of verification results.
        let runtime = Builder::new_current_thread()
            .thread_name("prusti-viper")
            .enable_all()
            .build()
            .expect("failed to construct Tokio runtime");
        verification_requests
            .map(|(program_name, request)| {
                let remote_result = runtime.block_on(client.verify(request));
                let result = remote_result.unwrap_or_else(|error| {
                    panic!("Verification request of program {program_name} failed: {error:?}")
                });
                (program_name, result)
            })
            .collect()
    } else {
        let mut stopwatch = Stopwatch::start("prusti-viper", "JVM startup");
        stopwatch.start_next("attach current thread to the JVM");
        let viper =
            Lazy::new(|| Viper::new_with_args(&config::viper_home(), config::extra_jvm_args()));
        let viper_thread = Lazy::new(|| viper.attach_current_thread());
        stopwatch.finish();
        let mut cache = PersistentCache::load_cache(config::cache_path());
        verification_requests
            .map(|(program_name, request)| {
                let result = process_verification_request(&viper_thread, request, &mut cache);
                (program_name, result)
            })
            .collect()
    }
}
