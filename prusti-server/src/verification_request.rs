// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{Backend, ServerMessage};
use log::info;
use prusti_rustc_interface::data_structures::fx::FxHashSet;
use prusti_utils::{
    config,
    report::log::{report, to_legal_file_name},
    Stopwatch,
};
use std::{
    fs::create_dir_all,
    path::PathBuf,
    sync::{self, mpsc, OnceLock},
};
use viper::{
    self, smt_manager::SmtManager, VerificationBackend, VerificationResult, VerificationResultKind,
    Viper,
};

/// The JVM object should only instantiated once, so it is stored in a
/// global reference, shareable between threads and execution of different
/// requests when running the server. No Mutex is used because
/// the value should only ever be used through non mutable references.
pub(crate) static VIPER: OnceLock<Viper> = OnceLock::new();

/// Server requests that are sent between client and server
/// These are oblivious to the backend being used for verification
/// and could potentially be something other than verification.
pub(crate) enum ServerRequest {
    Verification(ServerVerificationRequest),
}

/// Server requests that are sent between threads of the verifying process.
/// Specifies the kind of backend to be used for verification and carries necessary data.
pub(crate) enum ServerVerificationRequest {
    // viper program, backend config, set of viper identifiers
    JVMViperRequest(
        jni::objects::GlobalRef,
        ViperBackendConfig,
        FxHashSet<String>,
    ),
}

impl ServerVerificationRequest {
    /// Process and consume the request
    // FIXME: can we do without the "program" strings?
    pub fn process<'v, 't: 'v>(self, sender: &mpsc::Sender<ServerMessage>) {
        let mut stopwatch = Stopwatch::start("prusti-server", "verifier startup");
        let mut result = VerificationResult {
            item_name: "program".to_string(),
            kind: VerificationResultKind::Success,
            cached: false,
            time_ms: 0,
        };

        match self {
            ServerVerificationRequest::JVMViperRequest(
                viper_program_ref,
                backend_config,
                procedures,
            ) => {
                let viper = VIPER.get().expect("ServerVerificationRequest: Viper was not instantiated before processing a request");
                let verification_context = viper.attach_current_thread();
                let mut backend = match backend_config.backend {
                    VerificationBackend::Carbon | VerificationBackend::Silicon => Backend::Viper(
                        new_viper_verifier(
                            "program",
                            &verification_context,
                            backend_config.clone(),
                        ),
                        &verification_context,
                        viper_program_ref,
                    ),
                };
                stopwatch.start_next("backend verification");
                result.kind = backend.verify(procedures, sender.clone());
                result.time_ms = stopwatch.finish().as_millis();
            }
        }

        /*normalization_info.denormalize_result(&mut result.kind);*/
        sender.send(ServerMessage::Termination(result)).unwrap();
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct VerificationRequest {
    pub program: vir::ProgramRef,
    pub procedures: FxHashSet<String>,
    pub backend_config: ViperBackendConfig,
}

impl VerificationRequest {
    pub(crate) fn get_hash(&self) -> u64 {
        self.program.get_hash()
    }

    /// Builds a more specific request based on the backend configuration and sends it.
    /// This includes the vir-viper translation if the Viper backend is used.
    pub(crate) fn send(&self, mtx_tx_verreq: &sync::Mutex<mpsc::Sender<ServerRequest>>) {
        let request = self.build_request();

        mtx_tx_verreq
            .lock()
            .unwrap()
            .send(ServerRequest::Verification(request))
            .unwrap();
    }

    fn build_request(&self) -> ServerVerificationRequest {
        match self.backend_config.backend {
            VerificationBackend::Carbon | VerificationBackend::Silicon => {
                let mut stopwatch = Stopwatch::start("prusti-server backend", "JVM startup");
                let viper = VIPER.get_or_init(|| {
                    Viper::new_with_args(&config::viper_home(), config::extra_jvm_args())
                });
                stopwatch.start_next("attach current thread to the JVM");
                let context = viper.attach_current_thread();
                let ast_utils = context.new_ast_utils();

                stopwatch.start_next("construction of JVM objects");
                ast_utils.with_local_frame(16, || {
                    let ast_factory = context.new_ast_factory();

                    let viper_program = vir::with_vcx(|vcx| {
                        let program = vcx.get_program(self.program);
                        prusti_viper::program_to_viper(program, &ast_factory)
                    });

                    if config::dump_viper_program() {
                        stopwatch.start_next("dumping viper program");
                        dump_viper_program(
                            &ast_utils,
                            viper_program,
                            self.program.get_name_with_check_mode(),
                        );
                    }

                    let viper_program_ref = context
                        .env()
                        .new_global_ref(viper_program.to_jobject())
                        .unwrap();

                    ServerVerificationRequest::JVMViperRequest(
                        viper_program_ref,
                        self.backend_config.clone(),
                        self.procedures.clone(),
                    )
                })
            }
        }
    }
}

/// The configuration for the viper backend, (i.e. verifier).
/// Expresses which backend (silicon or carbon) should be used, and provides command-line arguments
/// to the viper verifier.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, Eq, PartialEq, Hash)]
pub struct ViperBackendConfig {
    pub backend: VerificationBackend,
    pub verifier_args: Vec<String>,
}

impl ViperBackendConfig {
    pub fn new(backend: VerificationBackend) -> Self {
        let mut verifier_args = config::extra_verifier_args();
        match backend {
            VerificationBackend::Silicon => {
                if config::use_more_complete_exhale() {
                    verifier_args.push("--enableMoreCompleteExhale".to_string());
                }
                if config::assume_injectivity_on_inhale() {
                    verifier_args.push("--assumeInjectivityOnInhale".to_string());
                }
                if config::counterexample() {
                    verifier_args.push("--counterexample".to_string());
                    verifier_args.push("mapped".to_string());
                }
                if let Some(number) = config::number_of_parallel_verifiers() {
                    verifier_args.push("--numberOfParallelVerifiers".to_string());
                    verifier_args.push(number.to_string());
                }

                verifier_args.extend(vec![
                    "--assertTimeout".to_string(),
                    config::assert_timeout().to_string(),
                    "--proverConfigArgs".to_string(),
                ]);
                // model.partial changes the default case of functions in counterexamples
                // to #unspecified
                let mut prover_args = format!(
                    "smt.qi.eager_threshold={} model.partial={}",
                    config::smt_qi_eager_threshold(),
                    config::counterexample()
                );

                if let Some(smt_qi_profile) = config::smt_qi_profile() {
                    prover_args = format!("{prover_args} smt.qi.profile={smt_qi_profile}");
                }
                if let Some(smt_qi_profile_freq) = config::smt_qi_profile_freq() {
                    prover_args =
                        format!("{prover_args} smt.qi.profile_freq={smt_qi_profile_freq}");
                }

                verifier_args.push(prover_args);

                verifier_args.extend(vec!["--logLevel".to_string(), "ERROR".to_string()]);

                if let Some(check_timeout) = config::check_timeout() {
                    verifier_args.push("--checkTimeout".to_string());
                    verifier_args.push(check_timeout.to_string());
                }

                if config::report_block_messages() && config::report_viper_messages() {
                    verifier_args.push("--generateBlockMessages".to_string());
                }
            }
            VerificationBackend::Carbon => {
                verifier_args.extend(vec!["--disableAllocEncoding".to_string()]);
            }
        }
        Self {
            backend,
            verifier_args,
        }
    }
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
            // TODO: unknown option?
            // verifier_args.extend(vec!["--disableTempDirectory".to_string()]);
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

pub fn dump_viper_program(
    ast_utils: &viper::AstUtils,
    program: viper::Program,
    program_name: &str,
) {
    let namespace = "viper_program";
    let filename = format!("{program_name}.vpr");
    info!("Dumping Viper program to '{namespace}/{filename}'");
    report(namespace, filename, ast_utils.pretty_print(program));
}
