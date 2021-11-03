// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::{
    config,
    report::log,
    verification_context::*,
    verification_service::ViperBackendConfig,
    vir::{Program, ToViper},
    Stopwatch,
};

pub struct VerifierRunner<'v> {
    context: VerificationContext<'v>,
    backend_config: &'v ViperBackendConfig,
}

impl<'v> VerifierRunner<'v> {
    pub fn new(
        verifier_builder: &'v VerifierBuilder,
        backend_config: &'v ViperBackendConfig,
    ) -> Self {
        let stopwatch = Stopwatch::start("prusti-server", "jvm attachment");
        let context = verifier_builder.new_verification_context();
        stopwatch.finish();
        Self {
            context,
            backend_config,
        }
    }

    pub fn verify(&self, program: Program) -> viper::VerificationResult {
        let ast_factory = self.context.new_ast_factory();
        let ast_utils = self.context.new_ast_utils();
        ast_utils.with_local_frame(16, || {
            // Create a new verifier each time.
            // Workaround for https://github.com/viperproject/prusti-dev/issues/744
            let mut stopwatch = Stopwatch::start("prusti-server", "verifier startup");
            let verifier = self.context.new_viper_verifier(self.backend_config);
            stopwatch.start_next("construction of JVM objects");
            let viper_program = program.to_viper(&ast_factory);
            if config::dump_viper_program() {
                stopwatch.start_next("dumping viper program");
                dump(&ast_utils, viper_program, &program.name);
            }
            stopwatch.start_next("verification");
            verifier.verify(viper_program)
        })
    }
}

fn dump(ast_utils: &viper::AstUtils, program: viper::Program, program_name: &str) {
    let namespace = "viper_program";
    let filename = format!("{}.vpr", program_name);
    info!("Dumping Viper program to '{}/{}'", namespace, filename);
    log::report(namespace, filename, ast_utils.pretty_print(program));
}
