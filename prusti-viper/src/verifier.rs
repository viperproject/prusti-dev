// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir::{optimizations::optimize_program};
use prusti_common::{
    config, report::log, Stopwatch, vir::program::Program,
};
use vir_crate::common::check_mode::CheckMode;
use crate::encoder::Encoder;
use crate::encoder::counterexamples::counterexample_translation;
use crate::encoder::counterexamples::counterexample_translation_refactored;
use prusti_interface::data::VerificationResult;
use prusti_interface::data::VerificationTask;
use prusti_interface::environment::Environment;
use prusti_interface::PrustiError;
use viper;

use prusti_interface::specs::typed;
use ::log::{info, debug, error};
use prusti_server::{VerificationRequest, PrustiClient, VerificationRequestProcessing, spawn_server_thread, ViperBackendConfig, ServerMessage};
use prusti_rustc_interface::span::DUMMY_SP;
use prusti_server::tokio::runtime::Builder;
use std::collections::HashMap;
use serde_json::json;
use async_stream::stream;
use futures_util::{Stream, StreamExt, pin_mut};

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
        def_spec: typed::DefSpecificationMap,
    ) -> Self {
        Verifier {
            env,
            encoder: Encoder::new(env, def_spec),
        }
    }

    pub fn verify(&mut self, task: &VerificationTask<'tcx>) -> VerificationResult {
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

        let polymorphic_programs = self.encoder.get_viper_programs();

        let mut programs: Vec<Program> = if config::simplify_encoding() {
            stopwatch.start_next("optimizing Viper program");
            let source_file_name = self.encoder.env().name.source_file_name();
            polymorphic_programs.into_iter().map(
                |program| Program::Legacy(optimize_program(program, &source_file_name).into())
            ).collect()
        } else {
            polymorphic_programs.into_iter().map(
                |program| Program::Legacy(program.into())
            ).collect()
        };
        programs.extend(self.encoder.get_core_proof_programs());

        stopwatch.start_next("verifying Viper program");

        let requests = self.programs_to_requests(programs);

        // runtime used either for client connecting to server sequentially
        // or to sequentially verify the requests -> single thread is sufficient
        // why single thread if everything is asynchronous? VerificationRequestProcessing in
        // prusti-server/src/process_verification.rs only has a single thread and the underlying
        // viper instance already uses as many cores as possible
        let rt = Builder::new_current_thread()
            .thread_name("prusti_viper_verifier_verify")
            .enable_all()
            .build()
            .unwrap();

        let mut overall_result = VerificationResult::Success;
        rt.block_on(async {
            overall_result = if let Some(server_address) = config::server_address() {
                let verification_messages = Self::verify_requests_server(requests, server_address);
                self.handle_stream(verification_messages).await
            } else {
                let vrp = VerificationRequestProcessing::new();
                let verification_messages = Self::verify_requests_local(requests, &vrp);
                self.handle_stream(verification_messages).await
            }
        });
        stopwatch.finish();
        overall_result
    }

    async fn handle_stream(&self, verification_messages: impl Stream<Item = (String, ServerMessage)>) -> VerificationResult {
        let mut overall_result = VerificationResult::Success;
        let encoding_errors_count = self.encoder.count_encoding_errors();
        let error_manager = self.encoder.error_manager();
        // we want quantifier_pos_ID + program_name + q_name as identifier because there are
        // different q_names for the same ID and each program reports independent results
        // key: (pos_id, program_name), key to result: q_name result: num_instantiations
        let mut quantifier_instantiations: HashMap::<(u64, String), HashMap::<String, u64>> = HashMap::new();

        // if we are not running in an ide, we want the errors to be reported sortedly
        let mut prusti_errors: Vec<_> = vec![];

        pin_mut!(verification_messages);

        while let Some((program_name, server_msg)) = verification_messages.next().await {
            match server_msg {
                ServerMessage::Termination(result) => match result {
                    // nothing to do
                    viper::VerificationResult::Success => (),
                    viper::VerificationResult::ConsistencyErrors(errors) => {
                        for error in errors {
                            PrustiError::internal(
                                format!("consistency error in {program_name}: {error}"), DUMMY_SP.into()
                            ).emit(&self.env.diagnostic);
                        }
                        overall_result = VerificationResult::Failure;
                    }
                    viper::VerificationResult::Failure(errors) => {
                        for verification_error in errors {
                            debug!("Verification error in {}: {:?}", program_name.clone(), verification_error);
                            let mut prusti_error = error_manager.translate_verification_error(&verification_error);

                            // annotate with counterexample, if requested
                            if config::counterexample() {
                                if config::unsafe_core_proof(){
                                    if let Some(silicon_counterexample) = &verification_error.counterexample {
                                        if let Some(def_id) = error_manager.get_def_id(&verification_error) {
                                            let counterexample = counterexample_translation_refactored::backtranslate(
                                                &self.encoder,
                                                error_manager.position_manager(),
                                                def_id,
                                                silicon_counterexample,
                                            );
                                            prusti_error = counterexample.annotate_error(prusti_error);
                                        } else {
                                            prusti_error = prusti_error.add_note(
                                                format!(
                                                    "the verifier produced a counterexample for {program_name}, but it could not be mapped to source code"
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
                                                "the verifier produced a counterexample for {program_name}, but it could not be mapped to source code"
                                            ),
                                            None,
                                        );
                                    }
                                }
                            }
                            debug!("Prusti error: {:?}", prusti_error);
                            if prusti_error.is_disabled() {
                                prusti_error.cancel();
                            } else {
                                if config::show_ide_info() {
                                    prusti_error.emit(&self.env.diagnostic);
                                } else {
                                    prusti_errors.push(prusti_error);
                                }
                            }
                        }
                        overall_result = VerificationResult::Failure;
                    }
                    viper::VerificationResult::JavaException(exception) => {
                        error!("Java exception: {}", exception.get_stack_trace());
                        PrustiError::internal(
                            format!("in {program_name}: {exception}"), DUMMY_SP.into()
                        ).emit(&self.env.diagnostic);
                        overall_result = VerificationResult::Failure;
                    }
                }
                ServerMessage::QuantifierInstantiation{q_name, insts, pos_id} => {
                    if config::report_qi_profile() {
                        match error_manager.position_manager().get_span_from_id(pos_id) {
                            Some(span) => {
                                let key = (pos_id, program_name.clone());
                                if !quantifier_instantiations.contains_key(&key) {
                                    quantifier_instantiations.insert(key.clone(), HashMap::new());
                                }
                                let map = quantifier_instantiations.get_mut(&key).unwrap();
                                // this replaces the old entry which is exactly what we want
                                map.insert(q_name, insts);
                                let mut n: u64 = 0;
                                for (_, insts) in map {
                                    n += *insts;
                                }
                                PrustiError::message(
                                    format!("quantifier_instantiations_message{}",
                                        json!({"instantiations": n, "method": program_name}),
                                    ), span.clone()
                                ).emit(&self.env.diagnostic);
                            },
                            None => info!("#{insts} quantifier instantiations of {q_name} for unknown position id {pos_id} in verification of {program_name}"),
                        }
                    }
                }
            }
        }

        // if we are in an ide, we already emit the errors asynchronously, otherwise we wait for
        // all of them in order to sort them
        if !config::show_ide_info() {
            prusti_errors.sort();

            for prusti_error in prusti_errors {
                debug!("Prusti error: {:?}", prusti_error);
                prusti_error.emit(&self.env.diagnostic);
            }
        }

        if encoding_errors_count != 0 {
            overall_result = VerificationResult::Failure;
        }
        overall_result
    }

    fn programs_to_requests(&self, programs: Vec<Program>) -> Vec<(String, VerificationRequest)> {
        let source_path = self.env.name.source_path();
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
            }.parse().unwrap();
            let request = VerificationRequest {
                program,
                backend_config: ViperBackendConfig::new(backend),
            };
            (program_name, request)
        });
        verification_requests.collect()
    }

    /// Returns a list of (program_name, verification_requests) tuples.
    fn verify_requests_server(verification_requests: Vec<(String, VerificationRequest)>, server_address: String)
        -> impl Stream<Item = (String, ServerMessage)>
    {
        let server_address = if server_address == "MOCK" {
            spawn_server_thread().to_string()
        } else {
            server_address
        };
        info!("Connecting to Prusti server at {}", server_address);
        let verification_stream = stream! {
            for (program_name, request) in verification_requests {
                yield PrustiClient::verify(server_address.clone(), request).await.map(move |msg| (program_name.clone(), msg));
            }
        };
        verification_stream.flatten()
    }

    fn verify_requests_local<'a>(verification_requests: Vec<(String, VerificationRequest)>, vrp: &'a VerificationRequestProcessing)
        -> impl Stream<Item = (String, ServerMessage)> + 'a
    {
        let verification_stream = stream! {
            for (program_name, request) in verification_requests {
                yield vrp.verify(request).map(move |msg| (program_name.clone(), msg));
            }
        };
        return verification_stream.flatten();
    }
}

