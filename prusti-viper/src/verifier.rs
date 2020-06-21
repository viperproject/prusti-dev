// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use prusti_common::{config, report::log, vir::Program, Stopwatch};
use prusti_filter::validators::Validator;
use prusti_interface::{
    data::{VerificationResult, VerificationTask},
    environment::Environment,
    specifications::TypedSpecificationMap,
};
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

    pub fn verify<F>(&mut self, task: &VerificationTask, verify: F) -> VerificationResult
    where
        F: FnOnce(Program) -> viper::VerificationResult,
    {
        info!(
            "Received {} functions to be verified:",
            task.procedures.len()
        );

        let stopwatch = Stopwatch::start("encoding to Viper");

        // Dump the configuration
        log::report("config", "prusti", config::dump());

        // Check support status, and queue encoding
        let validator = Validator::new(self.env.tcx());

        let report_support_status = config::report_support_status();
        let skip_unsupported_functions = config::skip_unsupported_functions();
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
                    // Avoid raising compiler errors for partially supported functions
                    false,
                    // Avoid raising compiler errors if we are going to skip unsupported functions
                    !skip_unsupported_functions,
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

        for &proc_id in task.procedures.iter().rev() {
            self.encoder.queue_procedure_encoding(proc_id);
        }
        self.encoder.process_encoding_queue();

        stopwatch.finish();

        let encoding_errors_count = self.encoder.count_encoding_errors();

        let mut program = self.encoder.get_viper_program();
        if config::simplify_encoding() {
            program = program.optimized();
        }
        let verification_result = verify(program);

        let verification_errors = match verification_result {
            viper::VerificationResult::Failure(errors) => errors,
            viper::VerificationResult::ConsistencyErrors(errors) => {
                errors.iter().for_each(|e| error!("{}", e));
                panic!("Consistency errors. The encoded Viper program is incorrect.");
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
