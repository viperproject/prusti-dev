// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::{Encoder, PrustiError};
use prusti_common::{
    config, report::log, verification_context::VerifierBuilder, verification_service::*, Stopwatch,
};
use prusti_filter::validators::Validator;
use prusti_interface::{
    data::{VerificationResult, VerificationTask},
    environment::Environment,
    specifications::TypedSpecificationMap,
};
use prusti_server::{PrustiServerConnection, ServerSideService, VerifierRunner};
use syntax_pos::DUMMY_SP;
use viper;

/// A verifier is an object for verifying a single crate, potentially
/// many times.
pub struct Verifier<'v, 'r, 'a, 'tcx>
where
    'r: 'v,
    'a: 'r,
    'tcx: 'a,
{
    env: &'v Environment<'r, 'a, 'tcx>,
    encoder: Encoder<'v, 'r, 'a, 'tcx>,
}

impl<'v, 'r, 'a, 'tcx> Verifier<'v, 'r, 'a, 'tcx> {
    pub fn new(env: &'v Environment<'r, 'a, 'tcx>, spec: &'v TypedSpecificationMap) -> Self {
        Verifier {
            env,
            encoder: Encoder::new(env, spec),
        }
    }

    pub fn verify(&mut self, task: &VerificationTask) -> VerificationResult {
        info!(
            "Received {} functions to be verified:",
            task.procedures.len()
        );

        let mut stopwatch = Stopwatch::start("encoding to Viper");

        // Dump the configuration
        log::report("config", "prusti", config::dump());

        // Check support status, and queue encoding
        let validator = Validator::new(self.env.tcx());

        let report_support_status = config::report_support_status();
        let skip_unsupported_functions = config::skip_unsupported_functions();
        let error_on_partially_supported = config::error_on_partially_supported();
        let mut skipped_functions_count = 0;

        for &proc_id in &task.procedures {
            let proc_name = self.env.get_absolute_item_name(proc_id);
            let proc_span = self.env.get_item_span(proc_id);
            let is_pure_function = self.env.has_attribute_name(proc_id, "pure");

            let support_status = if is_pure_function {
                validator.pure_function_support_status(proc_id)
            } else {
                validator.procedure_support_status(proc_id)
            };

            if report_support_status {
                support_status.report_support_status(
                    &self.env,
                    is_pure_function,
                    // true ==> raise compiler errors for partially supported functions
                    error_on_partially_supported,
                    // true ==> raise compiler errors for unsupported functions
                    error_on_partially_supported || !skip_unsupported_functions,
                );
            }

            if !support_status.is_supported() && skip_unsupported_functions {
                warn!(
                    "Skip verification of {}, as it is not fully supported.",
                    proc_name
                );
                self.env.span_warn_with_help_and_note(
                    proc_span,
                    &format!(
                        "this function will be ignored because it is not fully supported by \
                        Prusti: {}",
                        proc_name
                    ),
                    &Some(if report_support_status {
                        "Disable the SKIP_UNSUPPORTED_FUNCTIONS configuration flag to verify \
                            this function anyway."
                            .to_string()
                    } else {
                        "Enable the REPORT_SUPPORT_STATUS configuration flag for more details \
                            on why the function is not fully supported, or disable \
                            SKIP_UNSUPPORTED_FUNCTIONS to verify this function anyway."
                            .to_string()
                    }),
                    &None,
                );
                skipped_functions_count += 1;
            } else {
                self.encoder.queue_procedure_encoding(proc_id);
            }
        }
        info!(
            "Out of {} functions, {} are not fully supported and has been skipped.",
            task.procedures.len(),
            skipped_functions_count,
        );

        // Do the encoding
        self.encoder.process_encoding_queue();

        let encoding_errors_count = self.encoder.count_encoding_errors();
        let mut program = self.encoder.get_viper_program();

        if config::simplify_encoding() {
            stopwatch.start_next_section("optimizing Viper program");
            program = program.optimized();
        }

        stopwatch.start_next_section("verifying Viper program");
        let source_path = self.env.source_path();
        let program_name = source_path
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .to_owned();
        let verification_result: viper::VerificationResult =
            if let Some(server_address) = config::server_address() {
                let server_address = if server_address == "MOCK" {
                    ServerSideService::spawn_off_thread()
                } else {
                    server_address.parse().unwrap_or_else(|e| {
                        panic!("Invalid server address: {} (error: {})", server_address, e)
                    })
                };
                info!("Connecting to Prusti server at {}", server_address);
                let service = PrustiServerConnection::new(server_address);

                let request = VerificationRequest {
                    program,
                    program_name,
                    backend_config: Default::default(),
                };
                service.verify(request)
            } else {
                let mut stopwatch = Stopwatch::start("JVM startup");
                let verifier_builder = VerifierBuilder::new();
                stopwatch.start_next_section("running verifier");
                VerifierRunner::with_default_configured_runner(&verifier_builder, |runner| {
                    runner.verify(program, program_name.as_str())
                })
            };

        stopwatch.finish();

        let verification_errors = match verification_result {
            viper::VerificationResult::Failure(errors) => errors,
            viper::VerificationResult::ConsistencyErrors(errors) => {
                debug_assert!(!errors.is_empty());
                errors.iter().for_each(|e| {
                    PrustiError::internal(format!("consistency error: {}", e), DUMMY_SP.into())
                        .emit(self.env)
                });
                return VerificationResult::Failure;
            }
            viper::VerificationResult::Success() => vec![],
        };

        if encoding_errors_count == 0 && verification_errors.is_empty() {
            VerificationResult::Success
        } else {
            let error_manager = self.encoder.error_manager();

            for verification_error in verification_errors {
                debug!("Verification error: {:?}", verification_error);
                let prusti_error = error_manager.translate_verification_error(&verification_error);
                debug!("Prusti error: {:?}", prusti_error);
                prusti_error.emit(self.env);
            }
            VerificationResult::Failure
        }
    }
}
