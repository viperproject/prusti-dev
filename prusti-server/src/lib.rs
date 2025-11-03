#![feature(rustc_private)]
// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
#![warn(clippy::disallowed_types)]

use crate::{
    PrustiClient, ServerMessage, VerificationRequest, VerificationRequestProcessing,
    ViperBackendConfig,
};
use ::log::{debug, error, info};
use ide::IdeVerificationResult;
use once_cell::sync::Lazy;
use prusti_interface::{data::VerificationResult, environment::EnvDiagnostic, PrustiError};
use prusti_rustc_interface::{data_structures::fx::FxHashMap, span::DUMMY_SP};
use prusti_utils::{config, Stopwatch};
use viper::{self, Cache, PersistentCache};

mod client;
mod process_verification;
pub mod server;
mod server_message;
mod verification_request;
mod backend;

pub(crate) use backend::*;
pub(crate) use client::*;
pub(crate) use process_verification::*;
pub use server::{spawn_server_thread, start_server_on_port};
pub(crate) use server_message::*;
pub(crate) use verification_request::*;

// Futures returned by `Client` need to be executed in a compatible tokio runtime.
use async_stream::stream;
use futures_util::{pin_mut, Stream, StreamExt};
use serde_json::json;
use std::sync::{self, Arc};
pub use tokio;
use tokio::runtime::Builder;

/// Verify a list of programs.
pub fn verify_programs(
    env_diagnostic: &EnvDiagnostic<'_>,
    programs: Vec<vir::ProgramRef>,
) -> VerificationResult {
    let verification_requests = programs
        .into_iter()
        .map(|program| {
            let procedures = vir::with_vcx(|vcx| vcx.get_viper_identifiers());
            let backend = config::viper_backend().parse().unwrap();
            VerificationRequest {
                program,
                procedures,
                backend_config: ViperBackendConfig::new(backend),
            }
        })
        .collect();

    let stopwatch = Stopwatch::start("prusti-server", "verifying Viper program");
    // runtime used either for client connecting to server sequentially
    // or to sequentially verify the requests -> single thread is sufficient
    // why single thread if everything is asynchronous? VerificationRequestProcessing in
    // prusti-server/src/process_verification.rs only has a single thread and the underlying
    // viper instance already uses as many cores as possible
    let rt = Builder::new_current_thread()
        .thread_name("prusti-viper")
        .enable_all()
        .build()
        .expect("failed to construct Tokio runtime");

    let overall_result = rt.block_on(async {
        if let Some(server_address) = config::server_address() {
            let verification_messages =
                verify_requests_server(verification_requests, server_address);
            handle_stream(env_diagnostic, verification_messages).await
        } else {
            let cache = Lazy::new(move || {
                Arc::new(sync::Mutex::new(PersistentCache::load_cache(
                    config::cache_path(),
                )))
            });
            let vrp = Lazy::new(VerificationRequestProcessing::new);
            let verification_messages = verify_requests_local(verification_requests, &cache, &vrp);
            handle_stream(env_diagnostic, verification_messages).await
        }
    });
    stopwatch.finish();
    overall_result
}

async fn handle_stream(
    env_diagnostic: &EnvDiagnostic<'_>,
    verification_messages: impl Stream<Item = ServerMessage>,
) -> VerificationResult {
    let mut overall_result = VerificationResult::Success;
    // let encoding_errors_count = self.encoder.count_encoding_errors();

    // we want quantifier_pos_ID + program_name + q_name as identifier because there are
    // different q_names for the same ID and each program reports independent results
    // key: (pos_id, program_name), key to result: q_name result: num_instantiations
    let mut quantifier_instantiations: FxHashMap<(usize, String), FxHashMap<String, u64>> =
        FxHashMap::default();

    let mut prusti_errors: Vec<_> = vec![];

    pin_mut!(verification_messages);

    while let Some(server_msg) = verification_messages.next().await {
        match server_msg {
            ServerMessage::Termination(result) => handle_termination_message(
                env_diagnostic,
                result,
                &mut prusti_errors,
                &mut overall_result,
            ),
            ServerMessage::MethodTermination {
                viper_method_name,
                result,
                verification_time,
            } => handle_method_termination_message(
                env_diagnostic,
                viper_method_name,
                result,
                verification_time,
                &mut prusti_errors,
                &mut overall_result,
            ),
            ServerMessage::QuantifierInstantiation {
                q_name,
                insts,
                pos_id,
            } => handle_quantifier_instantiation_message(
                env_diagnostic,
                q_name,
                insts,
                pos_id,
                &mut quantifier_instantiations,
            ),
            ServerMessage::QuantifierChosenTriggers {
                viper_quant,
                triggers,
                pos_id,
            } => handle_quantifier_chosen_triggers_message(
                env_diagnostic,
                viper_quant,
                triggers,
                pos_id,
            ),
            ServerMessage::BlockReached {
                viper_method,
                vir_label,
                path_id,
            } => handle_block_processing_message(
                env_diagnostic,
                viper_method,
                Some(vir_label),
                path_id,
                None,
            ),
            ServerMessage::BlockFailure {
                viper_method,
                vir_label,
                path_id,
            } => handle_block_processing_message(
                env_diagnostic,
                viper_method,
                Some(vir_label),
                path_id,
                // for now, we don't report any details about failures here
                Some("Failure".to_owned()),
            ),
            ServerMessage::PathProcessed {
                viper_method,
                path_id,
                result: _,
            } => handle_block_processing_message(env_diagnostic, viper_method, None, path_id, None),
        }
    }

    // if we are in an ide, we already emit the errors asynchronously, otherwise we wait for
    // all of them because we want the errors to be reported sortedly
    if !config::show_ide_info() {
        prusti_errors.sort();

        for prusti_error in prusti_errors {
            debug!("Prusti error: {prusti_error:?}");
            prusti_error.emit(env_diagnostic);
        }
    }

    overall_result
}

fn handle_result(
    env_diagnostic: &EnvDiagnostic<'_>,
    result: viper::VerificationResult,
    prusti_errors: &mut Vec<PrustiError>,
    overall_result: &mut VerificationResult,
) {
    match result.kind {
        // nothing to do
        viper::VerificationResultKind::Success => (),
        viper::VerificationResultKind::ConsistencyErrors(errors) => {
            for error in errors {
                PrustiError::internal(format!("consistency error: {error:?}"), DUMMY_SP.into())
                    .emit(env_diagnostic);
            }
            *overall_result = VerificationResult::Failure;
        }
        viper::VerificationResultKind::Failure(errors) => {
            errors
                .into_iter()
                .flat_map(|error| {
                    prusti_encoder::backtranslate_error(
                        &error.full_id,
                        error.offending_pos_id.unwrap().parse::<usize>().unwrap(),
                        error.reason_pos_id.and_then(|id| id.parse::<usize>().ok()),
                    )
                    .expect("verification error could not be backtranslated")
                    .into_iter()
                })
                .for_each(|prusti_error| {
                    debug!("Prusti error: {prusti_error:?}");
                    if prusti_error.is_disabled() {
                        prusti_error.cancel();
                    } else if config::show_ide_info() {
                        prusti_error.emit(env_diagnostic);
                    } else {
                        prusti_errors.push(prusti_error);
                    }
                });

            *overall_result = VerificationResult::Failure;
        }
        viper::VerificationResultKind::JavaException(exception) => {
            error!("Java exception: {}", exception.get_stack_trace());
            PrustiError::internal(format!("in: {exception}"), DUMMY_SP.into()).emit(env_diagnostic);
            *overall_result = VerificationResult::Failure;
        }
    }
}

fn handle_method_termination_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    viper_method_name: String,
    result_kind: viper::VerificationResultKind,
    verification_time: u128,
    prusti_errors: &mut Vec<PrustiError>,
    overall_result: &mut VerificationResult,
) {
    if let Some(rust_method) = vir::with_vcx(|vcx| vcx.viper_to_rust_identifier(&viper_method_name))
    {
        let result = viper::VerificationResult {
            item_name: rust_method,
            kind: result_kind,
            cached: false,
            time_ms: verification_time,
        };

        handle_termination_message(env_diagnostic, result, prusti_errors, overall_result);
    } else {
        debug!(
            "Could not map method identifier to def id in termination message: {viper_method_name}"
        );
    }
}

fn handle_termination_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    result: viper::VerificationResult,
    prusti_errors: &mut Vec<PrustiError>,
    overall_result: &mut VerificationResult,
) {
    debug!(
        "Received termination message for {} with result {result:?} during verification",
        result.item_name
    );
    if config::show_ide_info() {
        PrustiError::message(
            format!(
                "ideVerificationResult{}",
                serde_json::to_string(&IdeVerificationResult {
                    item_name: result.item_name.clone(),
                    success: result.is_success(),
                    cached: result.cached,
                    time_ms: result.time_ms,
                })
                .unwrap()
            ),
            DUMMY_SP.into(),
        )
        .emit(env_diagnostic);
    }
    handle_result(env_diagnostic, result, prusti_errors, overall_result);
}

fn handle_quantifier_instantiation_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    q_name: String,
    insts: u64,
    pos_id: usize,
    quantifier_instantiations: &mut FxHashMap<(usize, String), FxHashMap<String, u64>>,
) {
    if config::report_viper_messages() {
        debug!("Received #{insts} quantifier instantiations of {q_name} for position id {pos_id} durign verification");
        vir::with_vcx(|vcx| {
            match vcx.get_span_from_id(pos_id) {
                Some(span) => {
                    let program_name = "program".to_owned();
                    let key = (pos_id, program_name.clone());
                    if !quantifier_instantiations.contains_key(&key) {
                        quantifier_instantiations.insert(key.clone(), FxHashMap::default());
                    }
                    let map = quantifier_instantiations.get_mut(&key).unwrap();
                    // for some reason, the aux quantifiers by the same z3 instance (same uniqueId
                    // in silicon) can have different amount of instantiations.
                    // e.g. we receive a message with 100 instantiations for a certain quantifier
                    // and afterwards a message with 20 instantiations for the same one.
                    // All verifying the same viper program and by the same z3 instance.
                    // Since I don see a better way to take this into account than taking the
                    // maximum, that is exactly what we do here.
                    let old_inst = map.get(&q_name).unwrap_or(&0);
                    map.insert(q_name, std::cmp::max(insts, *old_inst));
                    let mut n: u64 = 0;
                    for (q_name, insts) in map.iter() {
                        debug!("Key: {q_name}, Value: {insts}");
                        n += *insts;
                    }
                    PrustiError::message(
                        format!("quantifierInstantiationsMessage{}",
                            // TODO: in assistant, this quantifier message becomes an inlay hint at the given
                            // span. on hover of this inlay, a list of method names and their instantiation count
                            // for this range are displayed. currently, methods aren't resolved here, meaning the
                            // hover text will only display the isntantiations of the last message for the range.
                            // which is probably ok since all methods are in the same program. but the hover is useless.
                            // it should count which quantifier was instantiated how many times _by_ which method.
                            // resolving the method name here would merely tell what method the quantifier belongs
                            // to, not which one instantiated it. this is an artifact of verifying the entire program
                            // at once rather than having different programs for each method (as in the original PR).
                            // if it stays that way, the logic can be simplified.
                            json!({"instantiations": n, "method": "program"}),
                        ), span.into()
                    ).emit(env_diagnostic);
                },
                None => error!(
                  "#{insts} quantifier instantiations of {q_name} for unknown position id {pos_id} during verification"
                ),
            }
        });
    }
}

fn handle_quantifier_chosen_triggers_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    viper_quant: String,
    triggers: String,
    pos_id: usize,
) {
    if config::report_viper_messages() && pos_id != 0 {
        debug!("Received quantifier triggers {triggers} for quantifier {viper_quant} for position id {pos_id} during verification");
        vir::with_vcx(|vcx| {
            match vcx.get_span_from_id(pos_id) {
                Some(span) => {
                    PrustiError::message(
                        format!("quantifierChosenTriggersMessage{}",
                            json!({"viper_quant": viper_quant, "triggers": triggers}),
                        ), span.into()
                    ).emit(env_diagnostic);
                },
                None => error!("Invalid position id {pos_id} for viper quantifier {viper_quant} during verification"),
            }
        });
    }
}

fn handle_block_processing_message(
    env_diagnostic: &EnvDiagnostic<'_>,
    viper_method: String,
    vir_label: Option<String>,
    path_id: i32,
    result: Option<String>,
) {
    if config::report_viper_messages() && config::report_block_messages() {
        let token = if result.is_none() && vir_label.is_none() {
            "pathProcessedMessage"
        } else if result.is_none() {
            "blockReachedMessage"
        } else {
            "blockFailureMessage"
        };
        debug!("Received {token}: {{ method: {viper_method} message, vir_label: {vir_label:?}, path_id: {path_id}, result: {result:?} }}");

        vir::with_vcx(|vcx| {
            if let Some(def_id) = vcx.get_viper_identifier(&viper_method) {
                let rust_method = vcx.get_unique_item_name(&def_id);
                if let Some(vir_label) = vir_label {
                    if vir_label == "start" {
                        return;
                    }
                    let key = (def_id, vir_label);
                    if let Some(span) = vcx.get_block_span(&key) {
                        PrustiError::message(
                            format!("{}{}",
                                token,
                                if token == "blockFailureMessage" {
                                    json!({"method": rust_method, "path_id": path_id, "result": result.unwrap()})
                                } else {
                                    json!({"method": rust_method, "path_id": path_id})
                                },
                            ), span.into()
                        ).emit(env_diagnostic);
                    } else {
                        debug!(
                            "Could not map vir label {} to a position in {rust_method}",
                            key.1
                        )
                    }
                } else {
                    // no label means this is a pathProcessedMessage. This also covers the case of label == "end"
                    PrustiError::message(
                        format!(
                            "{}{}",
                            "pathProcessedMessage",
                            json!({"method": rust_method, "path_id": path_id})
                        ),
                        DUMMY_SP.into(),
                    )
                    .emit(env_diagnostic);
                }
            } else {
                debug!("Could not map method identifier to def id: {viper_method}")
            }
        })
    }
}

fn verify_requests_server(
    verification_requests: Vec<VerificationRequest>,
    server_address: String,
) -> impl Stream<Item = ServerMessage> {
    let server_address = if server_address == "MOCK" {
        spawn_server_thread().to_string()
    } else {
        server_address
    };
    info!("Connecting to Prusti server at {server_address}");
    let verification_stream = stream! {
        for request in verification_requests {
            yield PrustiClient::verify(server_address.clone(), request).await;
        }
    };
    verification_stream.flatten()
}

fn verify_requests_local<'a>(
    verification_requests: Vec<VerificationRequest>,
    cache: &'a Lazy<
        Arc<sync::Mutex<PersistentCache>>,
        impl FnOnce() -> Arc<sync::Mutex<PersistentCache>>,
    >,
    vrp: &'a Lazy<
        VerificationRequestProcessing,
        impl FnMut() -> VerificationRequestProcessing + 'a,
    >,
) -> impl Stream<Item = ServerMessage> + 'a {
    let verification_stream = stream! {
        for request in verification_requests {
            let request_hash = request.get_hash();
            if config::enable_cache() {
                if let Some(result) = Lazy::force(cache).get(request_hash) {
                    info!(
                        "Using cached result {:?}",
                        &result,
                    );
                    yield futures::stream::once(async move {
                        ServerMessage::Termination(result)
                    }).left_stream();
                }
            }
            yield vrp.verify(request).map(move |msg| {
                if let ServerMessage::Termination(result) = &msg {
                    if config::enable_cache() && !matches!(result.kind, viper::VerificationResultKind::JavaException(_)) {
                        info!(
                            "Storing new cached result {:?}",
                            &result,
                        );
                        cache.insert(request_hash, result.clone());
                    }
                }
                msg
            }).right_stream();
        }
    };
    verification_stream.flatten()
}
