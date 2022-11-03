// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::{
    config, report::log, Stopwatch, vir::program::Program,
};
use vir_crate::common::check_mode::CheckMode;
use prusti_interface::data::VerificationResult;
use prusti_interface::data::VerificationTask;
use prusti_interface::environment::Environment;
use prusti_interface::PrustiError;
use viper::{self, PersistentCache, Viper};
use prusti_interface::specs::typed;
use ::log::{info, debug, error};
use prusti_server::{VerificationRequest, PrustiClient, process_verification_request, spawn_server_thread, ViperBackendConfig};
use prusti_rustc_interface::span::DUMMY_SP;
use prusti_server::tokio::runtime::Builder;
use crate::encoder_interface::build_encoder;

/// Verify methods and types in a crate
pub fn verify_task<'tcx>(
    env: &Environment<'tcx>,
    def_spec: typed::DefSpecificationMap,
    task: &VerificationTask<'tcx>
) -> VerificationResult {
    info!("Received {} functions to be verified:", task.procedures.len());

    // Dump the configuration
    if config::dump_debug_info() {
        log::report("config", "prusti", config::dump());
    }

    let mut encoder = build_encoder(env, def_spec);

    // Encode the verification task
    for &proc_id in &task.procedures {
        let proc_name = env.name.get_absolute_item_name(proc_id);
        let proc_def_path = env.name.get_item_def_path(proc_id);
        let proc_span = env.query.get_def_span(proc_id);
        info!(" - {} ({})", proc_name, proc_def_path);
        info!("   Source: {:?}", proc_span);
    }
    let mut stopwatch = Stopwatch::start("prusti-viper", "encoding to Viper");
    let programs = encoder.encode_verification_task(task);

    let encoding_errors_count = encoder.count_encoding_errors();
    debug!("Number of encoding errors: {}", encoding_errors_count);

    stopwatch.start_next("verifying Viper program");
    let verification_results = verify_programs(env, programs);
    stopwatch.finish();

    // Group verification results
    let mut verification_errors : Vec<_> = vec![];
    let mut consistency_errors : Vec<_> = vec![];
    let mut java_exceptions : Vec<_> = vec![];
    for (name, result) in verification_results.into_iter() {
        match result {
            viper::VerificationResult::Success => {}
            viper::VerificationResult::ConsistencyErrors(errors) => {
                for error in errors.into_iter() {
                    consistency_errors.push((name.clone(), error));
                }
            }
            viper::VerificationResult::Failure(errors) => {
                for error in errors.into_iter() {
                    verification_errors.push((name.clone(), error));
                }
            }
            viper::VerificationResult::JavaException(exception) => {
                java_exceptions.push((name, exception));
            }
        }
    }

    // Convert verification results to Prusti errors
    let mut result = VerificationResult::Success;

    if encoding_errors_count != 0 {
        result = VerificationResult::Failure;
    }

    for (name, error) in consistency_errors.into_iter() {
        PrustiError::internal(
            format!("consistency error in {}: {}", name, error), DUMMY_SP.into()
        ).emit(&env.diagnostic);
        result = VerificationResult::Failure;
    }

    for (name, exception) in java_exceptions.into_iter() {
        error!("Java exception: {}", exception.get_stack_trace());
        PrustiError::internal(
            format!("Java exception in {}: {}", name, exception), DUMMY_SP.into()
        ).emit(&env.diagnostic);
        result = VerificationResult::Failure;
    }

    // Report verification errors
    let mut prusti_errors: Vec<_> = vec![];
    for (name, error) in &verification_errors {
        debug!("Verification error in {}: {:?}", name, error);
        let prusti_error = encoder.backtranslate_verification_error(error, name);
        prusti_errors.push(prusti_error);
    }
    prusti_errors.sort();

    for prusti_error in prusti_errors {
        debug!("Prusti error: {:?}", prusti_error);
        if prusti_error.is_disabled() {
            prusti_error.cancel();
        } else {
            prusti_error.emit(&env.diagnostic);
        }
        result = VerificationResult::Failure;
    }

    result
}

/// Verify a list of Viper programs.
/// Returns a list of (program_name, verification_result) tuples.
fn verify_programs(env: &Environment, programs: Vec<Program>)
    -> Vec<(String, viper::VerificationResult)>
{
    let source_path = env.name.source_path();
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
        program.set_name(format!("{}_{}", rust_program_name, program_name));
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
    if let Some(server_address) = config::server_address() {
        let server_address = if server_address == "MOCK" {
            spawn_server_thread().to_string()
        } else {
            server_address
        };
        info!("Connecting to Prusti server at {}", server_address);
        let client = PrustiClient::new(&server_address).unwrap_or_else(|error| {
            panic!(
                "Could not parse server address ({}) due to {:?}",
                server_address, error
            )
        });
        // Here we construct a Tokio runtime to block until completion of the futures returned by
        // `client.verify`. However, to report verification errors as early as possible,
        // `verify_programs` should return an asynchronous stream of verification results.
        let runtime = Builder::new_current_thread()
            .thread_name("prusti-viper")
            .enable_all()
            .build()
            .expect("failed to construct Tokio runtime");
        verification_requests.map(|(program_name, request)| {
            let remote_result = runtime.block_on(client.verify(request));
            let result = remote_result.unwrap_or_else(|error| {
                panic!(
                    "Verification request of program {} failed: {:?}",
                    program_name,
                    error
                )
            });
            (program_name, result)
        }).collect()
    } else {
        let mut stopwatch = Stopwatch::start("prusti-viper", "JVM startup");
        let viper = Viper::new_with_args(&config::viper_home(), config::extra_jvm_args());
        stopwatch.start_next("attach current thread to the JVM");
        let viper_thread = viper.attach_current_thread();
        stopwatch.finish();
        let mut cache = PersistentCache::load_cache(config::cache_path());
        verification_requests.map(|(program_name, request)| {
            let result = process_verification_request(&viper_thread, request, &mut cache);
            (program_name, result)
        }).collect()
    }
}
