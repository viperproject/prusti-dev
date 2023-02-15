// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{VerificationRequest, ViperBackendConfig, ServerMessage};
use log::info;
use prusti_common::{
    config,
    report::log::{report, to_legal_file_name},
    vir::{program_normalization::NormalizationInfo, ToViper},
    Stopwatch,
};
use std::{fs::create_dir_all, path::PathBuf, thread, sync::{mpsc, Arc, self}};
use viper::{
    smt_manager::SmtManager, PersistentCache, Cache, VerificationBackend, VerificationResult, VerificationResultType, Viper, VerificationContext, jni_utils::JniUtils
};
use viper_sys::wrappers::viper::*;
use viper_sys::wrappers::java;
use std::time;
use futures::{stream::Stream, lock};

enum ServerRequest {
    Verification(VerificationRequest),
    SaveCache,
}

pub struct VerificationRequestProcessing {
    mtx_rx_servermsg: lock::Mutex<mpsc::Receiver<ServerMessage>>,
    mtx_tx_verreq: sync::Mutex<mpsc::Sender<ServerRequest>>,
}

// one structure that lives for all the requests and has a single thread working on all the
// requests sequentially
// on reception of a verification request, we send it through a channel to the already running
// thread
impl VerificationRequestProcessing {
    pub fn new() -> Self {
        let (tx_servermsg, rx_servermsg) = mpsc::channel();
        let (tx_verreq, rx_verreq) = mpsc::channel();
        let mtx_rx_servermsg = lock::Mutex::new(rx_servermsg);
        let mtx_tx_verreq = sync::Mutex::new(tx_verreq);

        let ret = Self {mtx_rx_servermsg: mtx_rx_servermsg,
                        mtx_tx_verreq: mtx_tx_verreq,
                       };
        thread::spawn(|| { Self::verification_thread(rx_verreq, tx_servermsg) });
        ret
    }

    fn verification_thread(rx_verreq: mpsc::Receiver<ServerRequest>, tx_servermsg: mpsc::Sender<ServerMessage>) {
        let mut stopwatch = Stopwatch::start("verification_request_processing", "JVM startup");
        let viper = Arc::new(Viper::new_with_args(&config::viper_home(), config::extra_jvm_args()));
        let mut cache = PersistentCache::load_cache(config::cache_path());
        stopwatch.start_next("attach thread to JVM");
        let verification_context = viper.attach_current_thread();
        stopwatch.finish();
        loop {
            match rx_verreq.recv() {
                Ok(request) => {
                    match request {
                        ServerRequest::Verification(verification_request) =>
                            process_verification_request(&viper, &mut cache, &verification_context, &tx_servermsg, verification_request),
                        ServerRequest::SaveCache => cache.save(),
                    }
                }
                Err(_) => break,
            }
        }
    }

    pub fn verify<'a>(&'a self, request: VerificationRequest) -> impl Stream<Item = ServerMessage> + 'a {
        self.mtx_tx_verreq
            .lock()
            .unwrap()
            .send(ServerRequest::Verification(request))
            .unwrap();
        futures::stream::unfold(false, move |done: bool| async move {
            if done {
                return None;
            }
            let msg = self.mtx_rx_servermsg
                .lock()
                .await
                .recv()
                .unwrap();
            let mut done = false;
            if let ServerMessage::Termination(_) = msg {
                done = true;
            }
            Some((msg, done))
        })
    }

    pub fn save_cache(&self) {
        self.mtx_tx_verreq
            .lock()
            .unwrap()
            .send(ServerRequest::SaveCache)
            .unwrap();
    }
}
pub fn process_verification_request(
    viper_arc: &Arc<Viper>,
    cache: impl Cache,
    verification_context: &VerificationContext,
    sender: &mpsc::Sender<ServerMessage>,
    mut request: VerificationRequest,
) {
    let ast_utils = verification_context.new_ast_utils();

    // Only for testing: Check that the normalization is reversible.
    if config::print_hash() {
        debug_assert!({
            let mut program = request.program.clone();
            let normalization_info = NormalizationInfo::normalize_program(&mut program);
            normalization_info.denormalize_program(&mut program);
            program == request.program
        });
    }

    // Normalize the request before reaching the cache.
    let normalization_info = NormalizationInfo::normalize_program(&mut request.program);

    let hash = request.get_hash();
    info!(
        "Verification request hash: {} - for program {}",
        hash,
        request.program.get_name()
    );

    let build_or_dump_viper_program = || {
        let mut stopwatch = Stopwatch::start("prusti-server", "construction of JVM objects");
        let ast_factory = verification_context.new_ast_factory();
        let viper_program = request
            .program
            .to_viper(prusti_common::vir::LoweringContext::default(), &ast_factory);

        if config::dump_viper_program() {
            stopwatch.start_next("dumping viper program");
            dump_viper_program(
                &ast_utils,
                viper_program,
                &request.program.get_name_with_check_mode(),
            );
        }

        viper_program
    };

    // Only for testing: Print the hash and skip verification.
    if config::print_hash() {
        println!(
            "Received verification request for: {}",
            request.program.get_name()
        );
        println!("Hash of the request is: {hash}");
        // Some tests need the dump to report a diff of the Viper programs.
        if config::dump_viper_program() {
            ast_utils.with_local_frame(16, || {
                let _ = build_or_dump_viper_program();
            });
        }
        sender.send(ServerMessage::Termination(VerificationResult::dummy_success())).unwrap();
        return;
    }

    let mut result = VerificationResult{
        item_name : request.program.get_name().to_string(),
        result_type: VerificationResultType::Success,
        cached: false,
        time_ms: 0
    };

    // Early return in case of cache hit
    if config::enable_cache() {
        if let Some(mut result) = cache.get(hash) {
            info!(
                "Using cached result {:?} for program {}",
                &result,
                request.program.get_name()
            );
            if config::dump_viper_program() {
                ast_utils.with_local_frame(16, || {
                    let _ = build_or_dump_viper_program();
                });
            }
            result.cached = true;
            normalization_info.denormalize_result(&mut result.result_type);
            sender.send(ServerMessage::Termination(result)).unwrap();
            return;
        }
    };

    ast_utils.with_local_frame(16, || {
        let viper_program = build_or_dump_viper_program();
        let program_name = request.program.get_name();

        // Create a new verifier each time.
        // Workaround for https://github.com/viperproject/prusti-dev/issues/744
        let mut stopwatch = Stopwatch::start("prusti-server", "verifier startup");
        let mut verifier =
            new_viper_verifier(program_name, &verification_context, request.backend_config);

        stopwatch.start_next("verification");
        result.result_type = if config::report_viper_messages() {
            verify_and_poll_msgs(verification_context, verifier, viper_program, viper_arc, sender.clone())
        } else {
            verifier.verify(viper_program)
        };
        result.time_ms = stopwatch.finish().as_millis();

        // Don't cache Java exceptions, which might be due to misconfigured paths.
        if config::enable_cache() && !matches!(result.result_type, VerificationResultType::JavaException(_)) {
            info!(
                "Storing new cached result {:?} for program {}",
                &result,
                request.program.get_name()
            );
            cache.insert(hash, result.clone());
        }

        normalization_info.denormalize_result(&mut result.result_type);
        sender.send(ServerMessage::Termination(result)).unwrap();
    })
}

fn verify_and_poll_msgs(verification_context: &viper::VerificationContext,
                      mut verifier: viper::Verifier,
                      viper_program: viper::Program,
                      viper_arc: &Arc<Viper>,
                      sender: mpsc::Sender<ServerMessage>)
    -> VerificationResultType {
    let mut result_type = VerificationResultType::Success;
    // start thread for polling messages
    thread::scope(|scope| {
        // get the reporter
        let env = &verification_context.env();
        let jni = JniUtils::new(env);
        let verifier_wrapper = silver::verifier::Verifier::with(env);
        let reporter = jni.unwrap_result(verifier_wrapper.call_reporter(verifier.verifier_instance().clone()));
        let rep_glob_ref = env.new_global_ref(reporter).unwrap();

        let polling_thread = scope.spawn(|| polling_function(viper_arc, rep_glob_ref, sender));
        result_type = verifier.verify(viper_program);
        // FIXME: here the global ref is dropped from a detached thread
        polling_thread.join().unwrap();
    });
    result_type
}

fn polling_function(viper_arc: &Arc<Viper>,
                    rep_glob_ref: jni::objects::GlobalRef,
                    sender: mpsc::Sender<ServerMessage>) {
    let verification_context = viper_arc.attach_current_thread();
    let env = verification_context.env();
    let jni = JniUtils::new(env);
    let reporter_instance = rep_glob_ref.as_obj();
    let reporter_wrapper = silver::reporter::PollingReporter::with(env);
    loop {
        while reporter_wrapper.call_hasNewMessage(reporter_instance).unwrap() {
            let msg = reporter_wrapper.call_getNewMessage(reporter_instance).unwrap();
            match jni.class_name(msg).as_str() {
                "viper.silver.reporter.QuantifierInstantiationsMessage" => {
                    let msg_wrapper = silver::reporter::QuantifierInstantiationsMessage::with(env);
                    let q_name = jni.get_string(jni.unwrap_result(msg_wrapper.call_quantifier(msg)));
                    let q_inst = jni.unwrap_result(msg_wrapper.call_instantiations(msg));
                    info!("QuantifierInstantiationsMessage: {} {}", q_name, q_inst);
                    // also matches the "-aux" quantifiers generated
                    // we encoded the position id in the line and column number since this is not used by
                    // prusti either way
                    if q_name.starts_with("prog.l") {
                        let no_pref = q_name.strip_prefix("prog.l").unwrap();
                        let stripped = no_pref.strip_suffix("-aux").or(Some(no_pref)).unwrap();
                        let parsed = stripped.parse::<u64>();
                        match parsed {
                            Ok(pos_id) => {
                                sender.send(ServerMessage::QuantifierInstantiation{q_name: q_name,
                                                                                   insts: u64::try_from(q_inst).unwrap(),
                                                                                   pos_id: pos_id}
                                           ).unwrap();
                            }
                            _ => info!("Unexpected quantifier name {}", q_name)
                        }
                    }
                }
                "viper.silver.reporter.QuantifierChosenTriggersMessage" => {
                    let obj_wrapper = java::lang::Object::with(env);
                    let positioned_wrapper = silver::ast::Positioned::with(env);
                    let msg_wrapper = silver::reporter::QuantifierChosenTriggersMessage::with(env);

                    let viper_quant = jni.unwrap_result(msg_wrapper.call_quantifier(msg));
                    let viper_quant_str = jni.get_string(jni.unwrap_result(obj_wrapper.call_toString(viper_quant)));
                    // we encoded the position id in the line and column number since this is not used by
                    // prusti either way
                    let pos = jni.unwrap_result(positioned_wrapper.call_pos(viper_quant));
                    let pos_string = jni.get_string(jni.unwrap_result(obj_wrapper.call_toString(pos)));
                    let pos_id_index = pos_string.rfind(".").unwrap();
                    let pos_id = pos_string[pos_id_index+1..].parse::<u64>().unwrap();

                    let viper_triggers = jni.get_string(jni.unwrap_result(msg_wrapper.call_triggers__string(msg)));
                    info!("QuantifierChosenTriggersMessage: {} {} {}", viper_quant_str, viper_triggers, pos_id);
                    sender.send(ServerMessage::QuantifierChosenTriggers{viper_quant: viper_quant_str,
                                                                       triggers: viper_triggers,
                                                                       pos_id: pos_id}
                               ).unwrap();
                }
                "viper.silver.reporter.VerificationTerminationMessage" => return,
                _ => ()
            }
        }
        thread::sleep(time::Duration::from_millis(10));
    }
}

fn dump_viper_program(ast_utils: &viper::AstUtils, program: viper::Program, program_name: &str) {
    let namespace = "viper_program";
    let filename = format!("{program_name}.vpr");
    info!("Dumping Viper program to '{}/{}'", namespace, filename);
    report(namespace, filename, ast_utils.pretty_print(program));
}

fn new_viper_verifier<'v, 't: 'v>(
    program_name: &str,
    verification_context: &'v viper::VerificationContext<'t>,
    backend_config: ViperBackendConfig,
) -> viper::Verifier<'v> {
    let mut verifier_args: Vec<String> = backend_config.verifier_args;
    let report_path: Option<PathBuf>;
    if config::dump_debug_info() {
        let log_path = config::log_dir()
            .join("viper_tmp")
            .join(to_legal_file_name(program_name));
        create_dir_all(&log_path).unwrap();
        report_path = Some(log_path.join("report.csv"));
        let log_dir_str = log_path.to_str().unwrap();
        match backend_config.backend {
            VerificationBackend::Silicon => {
                verifier_args.extend(vec![
                    "--tempDirectory".to_string(),
                    log_dir_str.to_string(),
                    "--printMethodCFGs".to_string(),
                    //"--printTranslatedProgram".to_string(),
                ])
            }
            VerificationBackend::Carbon => verifier_args.extend(vec![
                "--boogieOpt".to_string(),
                format!("/logPrefix {log_dir_str}"),
                //"--print".to_string(), "./log/boogie_program/program.bpl".to_string(),
            ]),
        }
    } else {
        report_path = None;
        if backend_config.backend == VerificationBackend::Silicon {
            verifier_args.extend(vec!["--disableTempDirectory".to_string()]);
        }
    }
    let (smt_solver, smt_manager) = if config::use_smt_wrapper() {
        std::env::set_var("PRUSTI_ORIGINAL_SMT_SOLVER_PATH", config::smt_solver_path());
        let log_path = config::log_dir()
            .join("smt")
            .join(to_legal_file_name(program_name));
        create_dir_all(&log_path).unwrap();
        let smt_manager = SmtManager::new(
            log_path,
            config::preserve_smt_trace_files(),
            config::write_smt_statistics(),
            config::smt_qi_ignore_builtin(),
            config::smt_qi_bound_global_kind(),
            config::smt_qi_bound_trace(),
            config::smt_qi_bound_trace_kind(),
            config::smt_unique_triggers_bound(),
            config::smt_unique_triggers_bound_total(),
        );
        std::env::set_var(
            "PRUSTI_SMT_SOLVER_MANAGER_PORT",
            smt_manager.port().to_string(),
        );
        if config::log_smt_wrapper_interaction() {
            std::env::set_var("PRUSTI_LOG_SMT_INTERACTION", "true");
        }
        (config::smt_solver_wrapper_path(), smt_manager)
    } else {
        (config::smt_solver_path(), SmtManager::default())
    };
    let boogie_path = config::boogie_path();
    if let Some(bound) = config::smt_qi_bound_global() {
        // We need to set the environment variable to reach our Z3 wrapper.
        std::env::set_var("PRUSTI_SMT_QI_BOUND_GLOBAL", bound.to_string());
    }

    verification_context.new_verifier(
        backend_config.backend,
        verifier_args,
        report_path,
        smt_solver,
        boogie_path,
        smt_manager,
    )
}
