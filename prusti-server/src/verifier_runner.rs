use prusti_common::config;
use prusti_common::report::log;
use prusti_common::run_timed;
use prusti_viper::encoder::vir::Program;
use prusti_viper::verifier::{VerificationContext, VerifierBuilder};
use viper::{self, VerificationBackend, VerificationResult};

pub struct VerifierRunner<'v> {
    verifier: viper::Verifier<'v, viper::state::Started>,
    ast_factory: viper::AstFactory<'v>,
    ast_utils: viper::AstUtils<'v>,
}

impl<'v> VerifierRunner<'v> {
    pub fn with_runner<F>(verifier_builder: &VerifierBuilder, backend: VerificationBackend, body: F)
    where
        F: FnOnce(VerifierRunner),
    {
        let context = verifier_builder.new_verification_context();
        let runner = VerifierRunner::new(&context, backend);
        body(runner);
    }

    pub fn with_default_configured_runner<F>(verifier_builder: &VerifierBuilder, body: F)
    where
        F: FnOnce(VerifierRunner),
    {
        Self::with_runner(
            verifier_builder,
            VerificationBackend::from_str(&config::viper_backend()),
            body,
        )
    }

    fn new(context: &'v VerificationContext, backend: VerificationBackend) -> Self {
        Self {
            verifier: context.new_viper_verifier(backend),
            ast_factory: context.new_ast_factory(),
            ast_utils: context.new_ast_utils(),
        }
    }

    pub(crate) fn verify(&self, program: Program, program_name: &str) -> VerificationResult {
        let viper_program = run_timed("Construction of JVM objects successful", || {
            let viper_program = program.to_viper(&self.ast_factory);
            if config::dump_viper_program() {
                self.dump(viper_program, program_name);
            }
            viper_program
        });
        run_timed("Verification complete", || {
            self.verifier.verify(viper_program)
        })
    }

    fn dump(&self, program: viper::Program, program_name: &str) {
        let namespace = "viper_program";
        let filename = format!("{}.vpr", program_name);
        info!("Dumping Viper program to '{}/{}'", namespace, filename);
        log::report(namespace, filename, self.ast_utils.pretty_print(program));
    }
}
