// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::Program;
use encoder::Encoder;
use prusti_common::config;
use prusti_common::report::log;
use prusti_common::run_timed;
use prusti_filter::validators::Validator;
use prusti_interface::data::VerificationResult;
use prusti_interface::data::VerificationTask;
use prusti_interface::environment::Environment;
use prusti_interface::specifications::TypedSpecificationMap;
use std::fs::create_dir_all;
use std::path::PathBuf;
use verification_service::ViperBackendConfig;
use viper::{self, AstFactory, VerificationBackend, Viper};

/// A verifier builder is an object that lives entire program's
/// lifetime, has no mutable state, and is responsible for constructing
/// verification context instances. The user of this interface is supposed
/// to create a new verifier for each crate he or she wants to verify.
/// The main motivation for having a builder is to be able to cache the JVM
/// initialization.
pub struct VerifierBuilder {
    viper: Viper,
}

impl VerifierBuilder {
    pub fn new() -> Self {
        Self::new_with_backend(VerificationBackend::from_str(&config::viper_backend()))
    }

    pub fn new_with_backend(backend: VerificationBackend) -> Self {
        Self {
            viper: Viper::new_with_args(config::extra_jvm_args(), backend),
        }
    }

    pub fn new_verification_context(&self) -> VerificationContext {
        let verification_ctx = self.viper.new_verification_context();
        VerificationContext::new(verification_ctx)
    }
}

impl Default for VerifierBuilder {
    fn default() -> Self {
        VerifierBuilder::new()
    }
}

/// A verification context is an object that lives entire verification's lifetime.
/// Its main purpose is to build verifiers.
/// The main motivation for having a verification context is to be able to detach the current
/// thread from the JVM when the verification context goes out of scope.
pub struct VerificationContext<'v> {
    verification_ctx: viper::VerificationContext<'v>,
}

impl<'v, 'r, 'a, 'tcx> VerificationContext<'v>
where
    'r: 'v,
    'a: 'r,
    'tcx: 'a,
{
    fn new(verification_ctx: viper::VerificationContext<'v>) -> Self {
        VerificationContext { verification_ctx }
    }

    pub fn new_viper_verifier(
        &self,
        backend_config: &ViperBackendConfig,
    ) -> viper::Verifier<viper::state::Started> {
        // TODO: figure out how much of this should instead be determined on the client and thus done when creating the ViperBackendConfig

        let mut verifier_args: Vec<String> = vec![];
        let log_path: PathBuf = PathBuf::from(config::log_dir()).join("viper_tmp");
        create_dir_all(&log_path).unwrap();
        let report_path: PathBuf = log_path.join("report.csv");
        let log_dir_str = log_path.to_str().unwrap();
        // TODO: consider using if let instead
        match backend_config.backend {
            VerificationBackend::Silicon => {
                if config::use_more_complete_exhale() {
                    verifier_args.push("--enableMoreCompleteExhale".to_string());
                    // Buggy :(
                }
                verifier_args.extend(vec![
                    "--assertTimeout".to_string(),
                    config::assert_timeout().to_string(),
                    "--tempDirectory".to_string(),
                    log_dir_str.to_string(),
                    //"--logLevel".to_string(), "WARN".to_string(),
                ]);
            }
            VerificationBackend::Carbon => verifier_args.extend(vec![
                "--disableAllocEncoding".to_string(),
                "--boogieOpt".to_string(),
                format!("/logPrefix {}", log_dir_str),
            ]),
        }
        if config::dump_debug_info() {
            match backend_config.backend {
                VerificationBackend::Silicon => verifier_args.extend(vec![
                    "--printMethodCFGs".to_string(),
                    "--logLevel".to_string(),
                    "INFO".to_string(),
                    //"--printTranslatedProgram".to_string(),
                ]),
                VerificationBackend::Carbon => verifier_args.extend::<Vec<_>>(vec![
                    //"--print".to_string(), "./log/boogie_program/program.bpl".to_string(),
                ]),
            }
        }
        verifier_args.extend(backend_config.verifier_args.clone()); // TODO: is ordering important? would be nice to initialize verifier_args to this

        self.verification_ctx.new_verifier_with_args(
            backend_config.backend,
            verifier_args,
            Some(report_path),
        )
    }

    pub fn new_ast_factory(&self) -> AstFactory {
        self.verification_ctx.new_ast_factory()
    }

    pub fn new_ast_utils(&self) -> viper::AstUtils {
        self.verification_ctx.new_ast_utils()
    }
}

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
        run_timed("Encoding to Viper successful", || {
            // Dump the configuration
            log::report("config", "prusti", config::dump());

            let validator = Validator::new(self.env.tcx());

            info!("Received {} items to be verified:", task.procedures.len());

            for &proc_id in &task.procedures {
                let proc_name = self.env.get_absolute_item_name(proc_id);
                let proc_def_path = self.env.get_item_def_path(proc_id);
                let proc_span = self.env.get_item_span(proc_id);
                info!(" - {} from {:?} ({})", proc_name, proc_span, proc_def_path);
            }

            // Report support status
            if config::report_support_status() {
                for &proc_id in &task.procedures {
                    // Do some checks
                    let is_pure_function = self.env.has_attribute_name(proc_id, "pure");

                    let support_status = if is_pure_function {
                        validator.pure_function_support_status(proc_id)
                    } else {
                        validator.procedure_support_status(proc_id)
                    };

                    support_status.report_support_status(&self.env, is_pure_function, false);
                }
            }

            for &proc_id in task.procedures.iter().rev() {
                self.encoder.queue_procedure_encoding(proc_id);
            }
            self.encoder.process_encoding_queue();
        });

        let verification_result = verify(self.encoder.get_viper_program());

        let verification_errors = match verification_result {
            viper::VerificationResult::Failure(errors) => errors,
            viper::VerificationResult::ConsistencyErrors(errors) => {
                errors.iter().for_each(|e| error!("{}", e));
                panic!("Consistency errors. The encoded Viper program is incorrect.");
            }
            viper::VerificationResult::Success() => vec![],
        };

        if verification_errors.is_empty() {
            VerificationResult::Success
        } else {
            let error_manager = self.encoder.error_manager();

            for verification_error in verification_errors {
                debug!("Verification error: {:?}", verification_error);
                let compilation_error = error_manager.translate_verification_error(&verification_error);
                debug!("Compilation error: {:?}", compilation_error);
                self.env.span_err_with_help_and_note(
                    compilation_error.span,
                    &format!("[Prusti] {}", compilation_error.message),
                    &compilation_error.help,
                    &compilation_error.note,
                );
            }
            VerificationResult::Failure
        }
    }

    pub fn invalidate_all(&mut self) {
        unimplemented!()
    }
}
