#![feature(rustc_private)]

// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![warn(clippy::disallowed_types)]

use log::info;
use prusti_utils::{config, Stopwatch};
use viper::{PersistentCache, Viper};
use once_cell::sync::Lazy;

mod client;
mod process_verification;
mod server;
mod verification_request;
mod backend;

pub use backend::*;
pub use client::*;
pub use process_verification::*;
pub use server::*;
pub use verification_request::*;

// Futures returned by `Client` need to be executed in a compatible tokio runtime.
pub use tokio;

/// Verify a list of programs.
/// Returns a list of (program_name, verification_result) tuples.
pub fn verify_programs(programs: Vec<vir::ProgramRef>) -> Vec<(String, viper::VerificationResult)> {
    let verification_requests = programs.into_iter().map(|mut program| {
        let rust_program_name = program.get_rust_name().to_string();
        let program_name = program.get_name().to_string();
        // Prepend the Rust file name to the program.
        program.set_name(&format!("{rust_program_name}_{program_name}"));
        let backend = config::viper_backend().parse().unwrap();
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
            panic!("Could not parse server address ({server_address}) due to {error:?}")
        });
        // Here we construct a Tokio runtime to block until completion of the futures returned by
        // `client.verify`. However, to report verification errors as early as possible,
        // `verify_programs` should return an asynchronous stream of verification results.
        let runtime = tokio::runtime::Builder::new_current_thread()
            .thread_name("prusti-viper")
            .enable_all()
            .build()
            .expect("failed to construct Tokio runtime");
        verification_requests
            .map(|(program_name, request)| {
                let remote_result = runtime.block_on(client.verify(request));
                let result = remote_result.unwrap_or_else(|error| {
                    panic!("Verification request of program {program_name} failed: {error:?}")
                });
                (program_name, result)
            })
            .collect()
    } else {
        let mut stopwatch = Stopwatch::start("prusti-viper", "JVM startup");
        stopwatch.start_next("attach current thread to the JVM");
        let viper =
            Lazy::new(|| Viper::new_with_args(&config::viper_home(), config::extra_jvm_args()));
        let viper_thread = Lazy::new(|| viper.attach_current_thread());
        stopwatch.finish();

        let mut cache = PersistentCache::load_cache(config::cache_path());
        verification_requests
            .map(|(program_name, request)| {
                let result = process_verification_request(&viper_thread, request, &mut cache);
                (program_name, result)
            })
            .collect()
    }
}
