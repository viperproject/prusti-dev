// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(ip_constructors)]

extern crate reqwest;
extern crate viper;
extern crate warp;
#[macro_use]
extern crate log;
extern crate bincode;
extern crate futures;
extern crate lru;
extern crate prusti_common;
extern crate tokio;

mod service;
mod verifier_runner;
mod verifier_thread;

use lru::LruCache;
use prusti_common::{
    config, verification_context::VerifierBuilder, verification_service::*, Stopwatch,
};
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
        let stopwatch = Stopwatch::start("prusti-server", "JVM startup");
        let verifier_builder = Arc::new(VerifierBuilder::new());
        stopwatch.finish();

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
