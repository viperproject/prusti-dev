// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{Backend, ServerMessage, VerificationRequest, ViperBackendConfig};
use futures::{lock, stream::Stream};
use log::{debug, info};
use once_cell::sync::Lazy;
use prusti_common::{
    config,
    report::log::{report, to_legal_file_name},
    vir::{program_normalization::NormalizationInfo, ToViper},
    Stopwatch,
};
use std::{
    fs::create_dir_all,
    path::PathBuf,
    sync::{self, mpsc, Arc},
    thread,
};
use viper::{
    smt_manager::SmtManager, Cache, PersistentCache, VerificationBackend, VerificationContext,
    VerificationResult, VerificationResultKind, Viper,
};

enum ServerRequest {
    Verification(VerificationRequest),
    SaveCache,
}

struct ThreadJoin {
    handle: Option<thread::JoinHandle<()>>,
}

// we join the thread after dropping the sender for the ServerRequests, so
// that the verification thread actually terminates
impl Drop for ThreadJoin {
    fn drop(&mut self) {
        self.handle.take().unwrap().join().unwrap();
    }
}

pub struct VerificationRequestProcessing {
    mtx_rx_servermsg: lock::Mutex<mpsc::Receiver<ServerMessage>>,
    mtx_tx_verreq: sync::Mutex<mpsc::Sender<ServerRequest>>,
    // mtx_tx_verreq has to be dropped before thread_join
    #[allow(dead_code)]
    thread_join: ThreadJoin,
}

impl Default for VerificationRequestProcessing {
    fn default() -> Self {
        Self::new()
    }
}

/// A structure that lives for all the requests and has a single thread working on all the
/// requests sequentially.
/// On reception of a verification request, we send it through a channel to the already running
/// thread.
impl VerificationRequestProcessing {
    pub fn new() -> Self {
        let (tx_servermsg, rx_servermsg) = mpsc::channel();
        let (tx_verreq, rx_verreq) = mpsc::channel();
        let mtx_rx_servermsg = lock::Mutex::new(rx_servermsg);
        let mtx_tx_verreq = sync::Mutex::new(tx_verreq);

        let handle = thread::spawn(move || verification_thread(rx_verreq, tx_servermsg));
        Self {
            mtx_rx_servermsg,
            mtx_tx_verreq,
            thread_join: ThreadJoin {
                handle: Some(handle),
            },
        }
    }

    pub fn verify(&self, request: VerificationRequest) -> impl Stream<Item = ServerMessage> + '_ {
        self.mtx_tx_verreq
            .lock()
            .unwrap()
            .send(ServerRequest::Verification(request))
            .unwrap();
        // return a stream that has as last non-None message the ServerMessage::Termination
        futures::stream::unfold(false, move |done: bool| async move {
            if done {
                return None;
            }
            let msg = self.mtx_rx_servermsg.lock().await.recv().unwrap();
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

fn verification_thread(
    rx_verreq: mpsc::Receiver<ServerRequest>,
    tx_servermsg: mpsc::Sender<ServerMessage>,
) {
    debug!("Verification thread started.");
    let viper = Lazy::new(|| {
        Arc::new(Viper::new_with_args(
            &config::viper_home(),
            config::extra_jvm_args(),
        ))
    });
    let viper_thread = Lazy::new(|| viper.attach_current_thread());
    let mut cache = PersistentCache::load_cache(config::cache_path());

    while let Ok(request) = rx_verreq.recv() {
        match request {
            ServerRequest::Verification(verification_request) => process_verification_request(
                &viper,
                &viper_thread,
                &mut cache,
                &tx_servermsg,
                verification_request,
            ),
            ServerRequest::SaveCache => cache.save(),
        }
    }
    debug!("Verification thread finished.");
}

#[tracing::instrument(level = "debug", skip_all, fields(program = %request.program.get_name()))]
pub fn process_verification_request<'v, 't: 'v>(
    viper_arc: &Lazy<Arc<Viper>, impl Fn() -> Arc<Viper>>,
    verification_context: &'v Lazy<VerificationContext<'t>, impl Fn() -> VerificationContext<'t>>,
    cache: impl Cache,
    sender: &mpsc::Sender<ServerMessage>,
    mut request: VerificationRequest,
) {
    // TODO: if I'm not mistaken, this currently triggers the creation of the JVM on every request,
    // so this should be changed once there are actually backends that not use a JVM
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
        sender
            .send(ServerMessage::Termination(
                VerificationResult::dummy_success(),
            ))
            .unwrap();
        return;
    }

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
            normalization_info.denormalize_result(&mut result.kind);
            sender.send(ServerMessage::Termination(result)).unwrap();
            return;
        }
    };

    let mut stopwatch = Stopwatch::start("prusti-server", "verifier startup");

    // Create a new verifier each time.
    // Workaround for https://github.com/viperproject/prusti-dev/issues/744
    let mut backend = match request.backend_config.backend {
        VerificationBackend::Carbon | VerificationBackend::Silicon => Backend::Viper(
            new_viper_verifier(
                request.program.get_name(),
                verification_context,
                request.backend_config,
            ),
            verification_context,
            Lazy::force(viper_arc),
        ),
    };

    stopwatch.start_next("backend verification");
    let mut result = VerificationResult {
        item_name: request.program.get_name().to_string(),
        kind: VerificationResultKind::Success,
        cached: false,
        time_ms: 0,
    };
    result.kind = backend.verify(&request.program, sender.clone());
    result.time_ms = stopwatch.finish().as_millis();

    // Don't cache Java exceptions, which might be due to misconfigured paths.
    if config::enable_cache() && !matches!(result.kind, VerificationResultKind::JavaException(_)) {
        info!(
            "Storing new cached result {:?} for program {}",
            &result,
            request.program.get_name()
        );
        cache.insert(hash, result.clone());
    }

    normalization_info.denormalize_result(&mut result.kind);
    sender.send(ServerMessage::Termination(result)).unwrap();
}

pub fn dump_viper_program(
    ast_utils: &viper::AstUtils,
    program: viper::Program,
    program_name: &str,
) {
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
