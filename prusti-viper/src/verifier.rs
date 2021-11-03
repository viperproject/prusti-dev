// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir::{self, optimizations::optimize_program, ToViper, ToViperDecl};
use prusti_common::{
    config, report::log, verification_context::VerifierBuilder, verification_service::*, Stopwatch,
};
use crate::encoder::Encoder;
use crate::encoder::counterexample_translation;
// use prusti_filter::validators::Validator;
use prusti_interface::data::VerificationResult;
use prusti_interface::data::VerificationTask;
use prusti_interface::environment::Environment;
use prusti_interface::PrustiError;
// use prusti_interface::specifications::TypedSpecificationMap;
use std::time::Instant;
use viper::{self, VerificationBackend, Viper};
use std::path::PathBuf;
use std::fs::{create_dir_all, canonicalize};
use std::ffi::OsString;
use prusti_interface::specs::typed;
use ::log::{info, debug, error};
use prusti_server::{PrustiServerConnection, ServerSideService, VerifierRunner};
use rustc_span::DUMMY_SP;

// /// A verifier builder is an object that lives entire program's
// /// lifetime, has no mutable state, and is responsible for constructing
// /// verification context instances. The user of this interface is supposed
// /// to create a new verifier for each crate he or she wants to verify.
// /// The main motivation for having a builder is to be able to cache the JVM
// /// initialization.
// pub struct VerifierBuilder {
//     viper: Viper,
// }

// impl VerifierBuilder {
//     pub fn new() -> Self {
//         VerifierBuilder {
//             viper: Viper::new_with_args(
//                 config::extra_jvm_args(),
//                 VerificationBackend::from_str(&config::viper_backend())
//             ),
//         }
//     }

//     pub fn new_verification_context(&self) -> VerificationContext {
//         let verification_ctx = self.viper.new_verification_context();
//         VerificationContext::new(verification_ctx)
//     }
// }

// impl Default for VerifierBuilder {
//     fn default() -> Self {
//         VerifierBuilder::new()
//     }
// }

// /// A verification context is an object that lives entire verification's lifetime.
// /// Its main purpose is to build verifiers.
// /// The main motivation for having a verification context is to be able to detach the current
// /// thread from the JVM when the verification context goes out of scope.
// pub struct VerificationContext<'v> {
//     verification_ctx: viper::VerificationContext<'v>,
// }

// impl<'v, 'r, 'a, 'tcx> VerificationContext<'v>
//     where
//         'r: 'v,
//         'a: 'r,
//         'tcx: 'a,
// {
//     fn new(verification_ctx: viper::VerificationContext<'v>) -> Self {
//         VerificationContext { verification_ctx }
//     }

//     pub fn new_verifier(
//         &'v self,
//         env: &'v Environment<'tcx>,
//         spec: &'v typed::SpecificationMap<'tcx>,
//     ) -> Verifier<'v, 'tcx> {
//         let backend = VerificationBackend::from_str(&config::viper_backend());

//         let mut verifier_args: Vec<String> = vec![];
//         let log_path: PathBuf = PathBuf::from(config::log_dir()).join("viper_tmp");
//         create_dir_all(&log_path).unwrap();
//         let report_path: PathBuf = log_path.join("report.csv");
//         let log_dir_str = log_path.to_str().unwrap();
//         if let VerificationBackend::Silicon = backend {
//             if config::use_more_complete_exhale() {
//                 verifier_args.push("--enableMoreCompleteExhale".to_string()); // Buggy :(
//             }
//             verifier_args.extend(vec![
//                 "--assertTimeout".to_string(),
//                 config::assert_timeout().to_string(),
//                 "--tempDirectory".to_string(),
//                 log_dir_str.to_string(),
//                 //"--logLevel".to_string(), "WARN".to_string(),
//             ]);
//         } else {
//             verifier_args.extend(vec![
//                 "--disableAllocEncoding".to_string(),
//                 "--boogieOpt".to_string(),
//                 format!("/logPrefix {}", log_dir_str),
//             ]);
//         }
//         if config::dump_debug_info() {
//             if let VerificationBackend::Silicon = backend {
//                 verifier_args.extend(vec![
//                     "--printMethodCFGs".to_string(),
//                     "--logLevel".to_string(),
//                     "INFO".to_string(),
//                     //"--printTranslatedProgram".to_string(),
//                 ]);
//             } else {
//                 verifier_args.extend::<Vec<_>>(vec![
//                     //"--print".to_string(), "./log/boogie_program/program.bpl".to_string(),
//                 ]);
//             }
//         }
//         verifier_args.extend(config::extra_verifier_args());
//         Verifier::new(
//             self.verification_ctx.new_ast_utils(),
//             self.verification_ctx.new_ast_factory(),
//             self.verification_ctx
//                 .new_verifier_with_args(backend, verifier_args, Some(report_path)),
//             env,
//             spec,
//         )
//     }
// }

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
    pub fn new(
        env: &'v Environment<'tcx>,
        def_spec: &'v typed::DefSpecificationMap<'tcx>,
    ) -> Self {
        Verifier {
            env,
            encoder: Encoder::new(env, def_spec),
        }
    }

    pub fn verify(&mut self, task: &VerificationTask) -> VerificationResult {
        info!(
            "Received {} functions to be verified:",
            task.procedures.len()
        );

        let mut stopwatch = Stopwatch::start("prusti-viper", "encoding to Viper");

        // Dump the configuration
        if config::dump_debug_info() {
            log::report("config", "prusti", config::dump());
        }

        for &proc_id in &task.procedures {
            let proc_name = self.env.get_absolute_item_name(proc_id);
            let proc_def_path = self.env.get_item_def_path(proc_id);
            let proc_span = self.env.get_def_span(proc_id);
            info!(" - {} ({})", proc_name, proc_def_path);
            info!("   Source: {:?}", proc_span);
        }

        // // Check support status, and queue encoding
        // let validator = Validator::new(self.env.tcx());

        // let report_support_status = config::report_support_status();
        // let skip_unsupported_features = config::skip_unsupported_features();
        // let error_on_partially_supported = config::error_on_partially_supported();
        // let mut skipped_functions_count = 0;

        // for &proc_id in &task.procedures {
        //     let proc_name = self.env.get_absolute_item_name(proc_id);
        //     let proc_span = self.env.get_def_span(proc_id);
        //     let is_pure_function = self.env.has_prusti_attribute(proc_id, "pure");

        //     let support_status = if is_pure_function {
        //         validator.pure_function_support_status(proc_id)
        //     } else {
        //         validator.procedure_support_status(proc_id)
        //     };

        //     if report_support_status {
        //         support_status.report_support_status(
        //             &self.env,
        //             is_pure_function,
        //             // true ==> raise compiler errors for partially supported functions
        //             error_on_partially_supported,
        //             // true ==> raise compiler errors for unsupported functions
        //             error_on_partially_supported || !skip_unsupported_features,
        //         );
        //     }

        //     if !support_status.is_supported() && skip_unsupported_features {
        //         warn!(
        //             "Skip verification of {}, as it is not fully supported.",
        //             proc_name
        //         );
        //         self.env.span_warn_with_help_and_note(
        //             proc_span,
        //             &format!(
        //                 "this function will be ignored because it is not fully supported by \
        //                 Prusti: {}",
        //                 proc_name
        //             ),
        //             &Some(if report_support_status {
        //                 "Disable the SKIP_UNSUPPORTED_FEATURES configuration flag to verify \
        //                     this function anyway."
        //                     .to_string()
        //             } else {
        //                 "Enable the REPORT_SUPPORT_STATUS configuration flag for more details \
        //                     on why the function is not fully supported, or disable \
        //                     SKIP_UNSUPPORTED_FEATURES to verify this function anyway."
        //                     .to_string()
        //             }),
        //             &None,
        //         );
        //         skipped_functions_count += 1;
        //     } else {
        //         self.encoder.queue_procedure_encoding(proc_id);
        //     }
        // }
        // info!(
        //     "Out of {} functions, {} are not fully supported and have been skipped.",
        //     task.procedures.len(),
        //     skipped_functions_count,
        // );

        for &proc_id in task.procedures.iter().rev() {
            // FIXME: Use the loop above.
            self.encoder.queue_procedure_encoding(proc_id);
        }
        self.encoder.process_encoding_queue();

        let encoding_errors_count = self.encoder.count_encoding_errors();

        let polymorphic_programs = self.encoder.get_viper_programs();

        let programs: Vec<vir::Program> = if config::simplify_encoding() {
            stopwatch.start_next("optimizing Viper program");
            let source_file_name = self.encoder.env().source_file_name();
            polymorphic_programs.into_iter().map(
                |program| optimize_program(program, &source_file_name).into()
            ).collect()
        } else {
            polymorphic_programs.into_iter().map(
                |program| program.into()
            ).collect()
        };

        stopwatch.start_next("verifying Viper program");
        let verification_results = verify_programs(self.env, programs);
        stopwatch.finish();

        // Group verification results
        let mut verification_errors : Vec<_> = vec![];
        let mut consistency_errors : Vec<_> = vec![];
        let mut java_exceptions : Vec<_> = vec![];
        for (method_name, result) in verification_results.into_iter() {
            match result {
                viper::VerificationResult::Success => {}
                viper::VerificationResult::ConsistencyErrors(errors) => {
                    for error in errors.into_iter() {
                        consistency_errors.push((method_name.clone(), error));
                    }
                }
                viper::VerificationResult::Failure(errors) => {
                    for error in errors.into_iter() {
                        verification_errors.push((method_name.clone(), error));
                    }
                }
                viper::VerificationResult::JavaException(exception) => {
                    java_exceptions.push((method_name, exception));
                }
            }
        }

        // Convert verification results to Prusti errors
        let error_manager = self.encoder.error_manager();
        let mut result = VerificationResult::Success;

        for (method, error) in consistency_errors.into_iter() {
            PrustiError::internal(
                format!("consistency error in {}: {}", method, error), DUMMY_SP.into()
            ).emit(self.env);
            result = VerificationResult::Failure;
        }

        for (method, exception) in java_exceptions.into_iter() {
            error!("Java exception: {}", exception.get_stack_trace());
            PrustiError::internal(
                format!("in {}: {}", method, exception), DUMMY_SP.into()
            ).emit(self.env);
            result = VerificationResult::Failure;
        }

        // Report verification errors
        let mut prusti_errors: Vec<_> = vec![];
        for (method, verification_error) in verification_errors.into_iter() {
            debug!("Verification error in {}: {:?}", method, verification_error);
            let mut prusti_error = error_manager.translate_verification_error(&verification_error);

            // annotate with counterexample, if requested
            if config::produce_counterexample() {
                if let Some(silicon_counterexample) = &verification_error.counterexample {
                    if let Some(def_id) = error_manager.get_def_id(&verification_error) {
                        let counterexample = counterexample_translation::backtranslate(
                            &self.encoder,
                            *def_id,
                            silicon_counterexample,
                        );
                        prusti_error = counterexample.annotate_error(prusti_error);
                    } else {
                        prusti_error = prusti_error.add_note(
                            format!(
                                "the verifier produced a counterexample for {}, but it could not be mapped to source code",
                                method
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
                prusti_error.emit(self.env);
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
fn verify_programs(env: &Environment, programs: Vec<vir::Program>)
    -> Vec<(String, viper::VerificationResult)>
{
    let source_path = env.source_path();
    let rust_program_name = source_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_owned();
    // Prepend the Rust file name to the program.
    let renamed_programs = programs.into_iter().map(|program| {
        let program_name = program.name.clone();
        let renamed_program = vir::Program {
            name: format!("{}_{}", rust_program_name, program_name),
            ..program
        };
        (program_name, renamed_program)
    });
    if let Some(server_address) = config::server_address() {
        let server_address = if server_address == "MOCK" {
            ServerSideService::spawn_off_thread().to_string()
        } else {
            server_address
        };
        info!("Connecting to Prusti server at {}", server_address);
        let service = PrustiServerConnection::new(&server_address).unwrap_or_else(|error| {
            panic!(
                "Could not parse server address ({}) due to {:?}",
                server_address, error
            )
        });
        renamed_programs.map(|(program_name, program)| {
            let request = VerificationRequest {
                program,
                backend_config: Default::default(),
            };
            (program_name, service.verify(request))
        }).collect()
    } else {
        let mut stopwatch = Stopwatch::start("prusti-viper", "JVM startup");
        let verifier_builder = VerifierBuilder::new();
        stopwatch.start_next("running verifier");
        let config = ViperBackendConfig::default();
        let runner = VerifierRunner::new(&verifier_builder, &config);
        renamed_programs.map(|(program_name, program)| {
            (program_name, runner.verify(program))
        }).collect()
    }
}
