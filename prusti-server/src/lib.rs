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

pub mod service;
mod verifier_thread;

use prusti_viper::encoder::vir::Program;
use prusti_viper::verifier::VerifierBuilder;
use service::*;
use std::collections::HashMap;
use std::sync::Arc;
use verifier_thread::*;
use viper::{VerificationBackend, VerificationResult};

pub struct PrustiServer {
    verifier_builder: Arc<VerifierBuilder>,
    threads: HashMap<VerificationBackend, VerifierThread>,
}

impl PrustiServer {
    pub fn new() -> PrustiServer {
        debug!("Prepare verifier builder...");
        run_timed!("JVM startup",
            let verifier_builder = Arc::new(VerifierBuilder::new());
        );
        PrustiServer {
            verifier_builder,
            threads: HashMap::new(),
        }
    }

    pub fn run_verifier_async<F>(
        &mut self,
        program: Program,
        backend: VerificationBackend,
    ) -> FutVerificationResult {
        self.get_or_create_thread(backend).verify(program)
    }

    fn get_or_create_thread(&mut self, backend: VerificationBackend) -> &VerifierThread {
        if !self.threads.contains_key(&backend) {
            let thread = VerifierThread::new(self.verifier_builder.clone(), backend);
            self.threads.insert(backend, thread);
        }
        self.threads.get(&backend).unwrap()
    }

    pub fn run_verifier_sync(
        &self,
        program: Program,
        backend: VerificationBackend,
    ) -> VerificationResult {
        run_timed!("Verifier startup",
            let context = self.verifier_builder.new_verification_context();
            let verifier = context.new_viper_verifier(backend);
        );

        let ast_factory = context.new_ast_factory();
        let viper_program = program.to_viper(&ast_factory);

        // TODO: dump viper program if desired

        verifier.verify(viper_program)
    }
}
