// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{VerificationRequest, ViperBackendConfig};
use log::info;
use prusti_common::{
    config,
    report::log::{report, to_legal_file_name},
    vir::ToViper,
    Stopwatch,
};
use std::{fs::create_dir_all, path::PathBuf};
use viper::{
    smt_manager::SmtManager, Cache, VerificationBackend, VerificationContext, VerificationResult,
};

pub fn process_verification_request<'v, 't: 'v>(
    verification_context: &'v VerificationContext<'t>,
    request: VerificationRequest,
    cache: impl Cache,
) -> viper::VerificationResult {
    let ast_utils = verification_context.new_ast_utils();

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

    // Print the hash and skip verification. Used for testing.
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
        if let Some(result) = cache.get(hash) {
            if result != VerificationResult::Success {
                info!(
                    "cached result {:?} for program {}",
                    &result,
                    request.program.get_name()
                );
            }
            if config::dump_viper_program() {
                ast_utils.with_local_frame(16, || {
                    let _ = build_or_dump_viper_program();
                });
            }
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
            new_viper_verifier(program_name, verification_context, request.backend_config);

        stopwatch.start_next("verification");
        let result = verifier.verify(viper_program);

        if config::enable_cache() {
            if result != VerificationResult::Success {
                info!(
                    "storing new cached result {:?} for program {}",
                    &result,
                    request.program.get_name()
                );
            }
            cache.insert(hash, result.clone());
        }

        result
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
            config::smt_quantifier_instantiations_ignore_builtin(),
            config::smt_quantifier_instantiations_bound_global_kind(),
            config::smt_quantifier_instantiations_bound_trace(),
            config::smt_quantifier_instantiations_bound_trace_kind(),
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
    if let Some(bound) = config::smt_quantifier_instantiations_bound_global() {
        // We need to set the environment variable to reach our Z3 wrapper.
        std::env::set_var(
            "PRUSTI_SMT_QUANTIFIER_INSTANTIATIONS_BOUND_GLOBAL",
            bound.to_string(),
        );
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
