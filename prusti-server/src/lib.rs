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

mod service;
mod verifier_runner;
mod verifier_thread;

use prusti_viper::encoder::vir::Program;
use prusti_viper::verification_service::ViperBackendConfig;
use prusti_viper::verifier::VerifierBuilder;
pub use service::*;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
pub use verifier_runner::*;
use verifier_thread::*;

pub struct PrustiServer {
    verifier_builder: Arc<VerifierBuilder>,
    threads: RwLock<HashMap<ViperBackendConfig, VerifierThread>>,
}

impl PrustiServer {
    pub fn new() -> PrustiServer {
        debug!("Prepare verifier builder...");
        run_timed!("JVM startup",
            let verifier_builder = Arc::new(VerifierBuilder::new());
        );
        PrustiServer {
            verifier_builder,
            threads: RwLock::default(),
        }
    }

    pub fn run_verifier_async(
        &self,
        program: Program,
        backend_config: ViperBackendConfig,
    ) -> FutVerificationResult {
        // create new thread if none exists for given configuration
        if !self.threads.read().unwrap().contains_key(&backend_config) {
            let thread = VerifierThread::new(self.verifier_builder.clone(), backend_config.clone());
            self.threads
                .write()
                .unwrap()
                .insert(backend_config.clone(), thread);
        }
        // TODO: limit thread pool size, getting rid of disused threads when necessary.

        self.threads
            .read()
            .unwrap()
            .get(&backend_config)
            .unwrap()
            .verify(program)
    }
}
