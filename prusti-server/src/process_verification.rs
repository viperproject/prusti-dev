// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{VerificationRequest, ViperBackendConfig};
use log::info;
use prusti_common::{config, report::log::report, vir::ToViper, Stopwatch};
use std::{fs::create_dir_all, path::PathBuf};
use viper::{Cache, VerificationBackend, VerificationContext};

pub fn process_verification_request_cache<'v, 't: 'v>(
    verification_context: &'v VerificationContext<'t>,
    request: VerificationRequest,
    cache: impl Cache,
) -> viper::VerificationResult {
    if !config::enable_cache() || config::print_hash() {
        process_verification_request(verification_context, request)
    } else {
        let hash = request.get_hash();
        info!("Verification request hash: {}", hash);
        // Try to load from cache and return `result`
        if let Some(result) = cache.get(hash) {
            info!("Using verification result from the cache");
            return result;
        }
        let result = process_verification_request(verification_context, request);
        // Save `result` to cache
        cache.insert(hash, result.clone());
        result
    }
}

pub fn process_verification_request<'v, 't: 'v>(
    verification_context: &'v VerificationContext<'t>,
    request: VerificationRequest,
) -> viper::VerificationResult {
    // Print hash of the `VerificationRequest`
    if config::print_hash() {
        println!(
            "Received verification request for: {}",
            request.program.get_name()
        );
        println!("Hash of the request is: {}", request.get_hash());
        // Skip actual verification
        if !config::dump_viper_program() {
            return viper::VerificationResult::Success;
        }
    }

    let ast_utils = verification_context.new_ast_utils();
    ast_utils.with_local_frame(16, || {
        // Create a new verifier each time.
        // Workaround for https://github.com/viperproject/prusti-dev/issues/744
        let mut stopwatch = Stopwatch::start("prusti-server", "verifier startup");
        let verifier = new_viper_verifier(verification_context, request.backend_config);
        stopwatch.start_next("construction of JVM objects");
        let ast_factory = verification_context.new_ast_factory();
        let viper_program = request.program.to_viper(&ast_factory);
        if config::dump_viper_program() {
            stopwatch.start_next("dumping viper program");
            dump_program(&ast_utils, viper_program, request.program.get_name());
            if config::print_hash() {
                return viper::VerificationResult::Success;
            }
        }
        stopwatch.start_next("verification");
        verifier.verify(viper_program)
    })
}

fn dump_program(ast_utils: &viper::AstUtils, program: viper::Program, program_name: &str) {
    let namespace = "viper_program";
    let filename = format!("{}.vpr", program_name);
    info!("Dumping Viper program to '{}/{}'", namespace, filename);
    report(namespace, filename, ast_utils.pretty_print(program));
}

fn new_viper_verifier<'v, 't: 'v>(
    verification_context: &'v viper::VerificationContext<'t>,
    backend_config: ViperBackendConfig,
) -> viper::Verifier<'v> {
    let mut verifier_args: Vec<String> = backend_config.verifier_args;
    let report_path: Option<PathBuf>;
    if config::dump_debug_info() {
        let log_path = config::log_dir().join("viper_tmp");
        create_dir_all(&log_path).unwrap();
        report_path = Some(log_path.join("report.csv"));
        let log_dir_str = log_path.to_str().unwrap();
        match backend_config.backend {
            VerificationBackend::Silicon => verifier_args.extend(vec![
                "--tempDirectory".to_string(),
                log_dir_str.to_string(),
                "--printMethodCFGs".to_string(),
                //"--printTranslatedProgram".to_string(),
            ]),
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

    verification_context.new_verifier_with_args(backend_config.backend, verifier_args, report_path)
}
