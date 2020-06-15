// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(plugin, use_extern_macros, proc_macro_path_invoc)]
#![plugin(tarpc_plugins)]

#[macro_use]
extern crate tarpc;
extern crate prusti_viper;
extern crate viper;
#[macro_use]
extern crate log;
extern crate serde;
extern crate serde_derive;
extern crate serde_json;
#[macro_use]
extern crate prusti_common;
extern crate futures;
extern crate lru;

mod service;
mod verifier_runner;
mod verifier_thread;

use lru::LruCache;
use prusti_common::config;
use prusti_viper::verification_service::*;
use prusti_viper::verifier::VerifierBuilder;
pub use service::*;
use std::sync::{Arc, RwLock};
pub use verifier_runner::*;
use verifier_thread::*;

pub struct PrustiServer {
    verifier_builder: Arc<VerifierBuilder>,
    threads: RwLock<LruCache<ViperBackendConfig, VerifierThread>>,
}

impl PrustiServer {
    pub fn new() -> PrustiServer {
        debug!("Prepare verifier builder...");
        run_timed!("JVM startup",
            let verifier_builder = Arc::new(VerifierBuilder::new());
        );
        let thread_cache = LruCache::new(config::server_max_stored_verifiers());
        PrustiServer {
            verifier_builder,
            threads: RwLock::new(thread_cache),
        }
    }

    pub fn run_verifier_async(&self, request: VerificationRequest) -> FutVerificationResult {
        // create new thread if none exists for given configuration
        if !self
            .threads
            .read()
            .unwrap()
            .contains(&request.backend_config)
        {
            let thread = VerifierThread::new(
                self.verifier_builder.clone(),
                request.backend_config.clone(),
            );
            self.threads
                .write()
                .unwrap()
                .put(request.backend_config.clone(), thread);
        }

        self.threads
            .write()
            .unwrap()
            .get(&request.backend_config)
            .unwrap()
            .verify(request.program, request.program_name)
    }
}
