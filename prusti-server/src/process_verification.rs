// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{VerificationRequest, ViperBackendConfig, jni_utils::JniUtils};
use log::info;
use prusti_common::{
    config,
    report::log::{report, to_legal_file_name},
    vir::{program_normalization::NormalizationInfo, ToViper},
    Stopwatch,
};
use std::{fs::create_dir_all, path::PathBuf, thread, sync::Arc, collections::HashMap};
use viper::{
    smt_manager::SmtManager, Cache, VerificationBackend, VerificationResult, Viper,
};
use viper_sys::wrappers::viper::*;
use std::time;
use std::sync::mpsc;

pub fn process_verification_request<'v, 't: 'v>(
    viper_arc: &Arc<Viper>,
    mut request: VerificationRequest,
    cache: impl Cache,
) -> viper::VerificationResult {
    let stopwatch = Stopwatch::start("prusti-server", "attach thread to JVM");
    let verification_context = viper_arc.attach_current_thread();
    stopwatch.finish();
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
        println!("Hash of the request is: {}", hash);
        // Some tests need the dump to report a diff of the Viper programs.
        if config::dump_viper_program() {
            ast_utils.with_local_frame(16, || {
                let _ = build_or_dump_viper_program();
            });
        }
        return viper::VerificationResult::Success;
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
            normalization_info.denormalize_result(&mut result);
            return result;
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

        // get the reporter
        let env = &verification_context.env();
        let jni = JniUtils::new(env);
        let verifier_wrapper = silver::verifier::Verifier::with(env);
        let reporter = jni.unwrap_result(verifier_wrapper.call_reporter(verifier.verifier_instance().clone()));
        let rep_glob_ref = env.new_global_ref(reporter).unwrap();

        let viper_arc_clone = Arc::clone(&viper_arc);
        //let program_clone = request.program.clone();
        let normalization_info_clone = normalization_info.clone();
        let (main_tx, thread_rx) = mpsc::channel();
        let (thread_tx, main_rx) = mpsc::channel();

        // start thread for polling messages and print on receive
        // TODO: maybe change to scope thread?
        let polling_thread = thread::spawn(move || {
            /*let functions = match program_clone {
                program::Program::Legacy(p) => p.functions,
                program::Program::Low(_) => panic!("Program::Low not yet supported!"),
            };*/
            let verification_context = viper_arc_clone.attach_current_thread();
            let env = verification_context.env();
            let jni = JniUtils::new(env);
            let reporter_instance = rep_glob_ref.as_obj();
            let reporter_wrapper = silver::reporter::PollingReporter::with(env);
            let mut done = false;
            let mut q_insts = HashMap::<(u64, String), u64>::new();
            while !done {
                while reporter_wrapper.call_hasNewMessage(reporter_instance).unwrap() {
                    let msg = reporter_wrapper.call_getNewMessage(reporter_instance).unwrap();
                    //println!("{}", jni.class_name(msg).as_str());
                    match jni.class_name(msg).as_str() {
                        /*
                        "viper.silver.reporter.EntitySuccessMessage" => {
                            let msg_wrapper = silver::reporter::EntitySuccessMessage::with(env);
                            let verification_time = jni.unwrap_result(msg_wrapper.call_verificationTime(msg));
                            //let cached = jni.unwrap_result(msg_wrapper.call_cached(msg));
                            //println!("Received EntitySuccessMessage with time: {}", verification_time);
                            let concerning = jni.unwrap_result(msg_wrapper.call_concerning(msg));
                            let member_wrapper = silver::ast::Member::with(env);
                            //println!("Concerning: {}", jni.get_string(jni.unwrap_result(member_wrapper.call_name(concerning))));
                            match jni.class_name(concerning).as_str() {
                                "viper.silver.ast.Function" => {
                                    let name = jni.get_string(jni.unwrap_result(member_wrapper.call_name(concerning)));
                                    for f in &functions {
                                        if let Some(expr) = &f.body {
                                            if f.name == name {
                                                println!("SUCCESS: Function: {}, time: {}, body_pos: {:?}", name, verification_time, expr.pos());
                                            }
                                        }
                                    }
                                }
                                _ => ()
                            }
                        }
                        "viper.silver.reporter.EntityFailureMessage" => {
                            let msg_wrapper = silver::reporter::EntityFailureMessage::with(env);
                            let verification_time = jni.unwrap_result(msg_wrapper.call_verificationTime(msg));
                            //let cached = jni.unwrap_result(msg_wrapper.call_cached(msg));
                            //println!("Received EntityFailureMessage with time: {}", verification_time);
                            let concerning = jni.unwrap_result(msg_wrapper.call_concerning(msg));
                            let member_wrapper = silver::ast::Member::with(env);
                            //println!("Concerning: {}", jni.get_string(jni.unwrap_result(member_wrapper.call_name(concerning))));
                            match jni.class_name(concerning).as_str() {
                                "viper.silver.ast.Function" => {
                                    let name = jni.get_string(jni.unwrap_result(member_wrapper.call_name(concerning)));
                                    for f in &functions {
                                        if let Some(expr) = &f.body {
                                            if f.name == name {
                                                println!("FAILURE: Function: {}, time: {}, body_pos: {:?}", name, verification_time, expr.pos());
                                            }
                                        }
                                    }
                                }
                                _ => ()
                            }
                        }*/
                        "viper.silver.reporter.QuantifierInstantiationsMessage" => {
                            let msg_wrapper = silver::reporter::QuantifierInstantiationsMessage::with(env);
                            let q_name = jni.get_string(jni.unwrap_result(msg_wrapper.call_quantifier(msg)));
                            // also matches the "-aux" quantifiers generated
                            // problem: we want to keep the aux and non-aux version apart
                            if q_name.starts_with("quant_with_posID") {
                                let no_pref = q_name.strip_prefix("quant_with_posID").unwrap();
                                let stripped = no_pref.strip_suffix("-aux").or(Some(no_pref)).unwrap();
                                let parsed = stripped.parse::<u64>();
                                match parsed {
                                    Ok(pos_id) => {
                                        let norm_pos_id = normalization_info_clone.denormalize_position_id(pos_id);
                                        let q_inst = jni.unwrap_result(msg_wrapper.call_instantiations(msg));
                                        info!("QuantifierInstantiationsMessage: {} {} {} {}", q_name, q_inst, pos_id, norm_pos_id);
                                        // insert also updates the entry
                                        q_insts.insert((norm_pos_id, q_name), q_inst.try_into().unwrap());
                                        ()
                                    }
                                    _ => info!("Unexpected quantifier name {}", q_name)
                                }
                            }
                        }
                        _ => ()
                    }
                }
                if !thread_rx.try_recv().is_err() {
                    info!("Received termination signal!");
                    done = true;
                } else {
                    thread::sleep(time::Duration::from_millis(10));
                }
            }
            thread_tx.send(q_insts).unwrap();
        });
        stopwatch.start_next("verification");
        let mut result = verifier.verify(viper_program);

        main_tx.send(true).unwrap();
        let q_insts: HashMap<(u64, String), u64> = main_rx.recv().unwrap();
        polling_thread.join().unwrap();

        // Don't cache Java exceptions, which might be due to misconfigured paths.
        if config::enable_cache() && !matches!(result, VerificationResult::JavaException(_)) {
            info!(
                "Storing new cached result {:?} for program {}",
                &result,
                request.program.get_name()
            );
            cache.insert(hash, result.clone());
        }

        normalization_info.denormalize_result(&mut result);
        let enriched_result = match result {
            VerificationResult::Success => {
                info!("Enriching result");
                for ((pos_id, q_name), n) in q_insts.iter() {
                    info!("({} {}) {}", pos_id, q_name, n);
                }
                VerificationResult::EnrichedSuccess(q_insts)
            },
            VerificationResult::Failure(errors)=> {
                info!("Enriching result");
                for ((pos_id, q_name), n) in q_insts.iter() {
                    info!("({} {}) {}", pos_id, q_name, n);
                }
                VerificationResult::EnrichedFailure(errors, q_insts)
            },
            _ => result,
        };
        enriched_result
    })
}

fn dump_viper_program(ast_utils: &viper::AstUtils, program: viper::Program, program_name: &str) {
    let namespace = "viper_program";
    let filename = format!("{}.vpr", program_name);
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
                format!("/logPrefix {}", log_dir_str),
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
