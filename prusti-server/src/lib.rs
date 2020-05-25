#![feature(plugin, use_extern_macros, proc_macro_path_invoc)]
#![plugin(tarpc_plugins)]

#[macro_use]
extern crate tarpc;
extern crate prusti_viper;
extern crate viper;
#[macro_use]
extern crate log;
extern crate serde;
extern crate serde_json;
extern crate serde_derive;
#[macro_use]
extern crate prusti_interface;

use prusti_viper::encoder::vir::Program;
use prusti_viper::verifier::VerifierBuilder;

pub mod service;

pub struct PrustiServer {
    verifier_builder: VerifierBuilder,
    // store JavaVM
    // store GlobalVerifier for last-used verifier
    // store mutex for verifier access
}

impl PrustiServer {
    pub fn new() -> PrustiServer {
        debug!("Prepare verifier builder...");
        run_timed!("JVM startup",
            let verifier_builder = VerifierBuilder::new();
        );
        PrustiServer { verifier_builder }
    }

    pub fn run_verifier(
        &self,
        program: Program,
        backend: viper::VerificationBackend,
    ) -> viper::VerificationResult {
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
