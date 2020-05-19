#[macro_use]
extern crate log;
extern crate prusti_viper;
extern crate viper;

use prusti_viper::encoder::vir::Program;
use prusti_viper::verifier::VerifierBuilder;
use std::time::Instant;

pub struct PrustiServer {
    verifier_builder: VerifierBuilder,
}

macro_rules! run_timed {
    ($desc:expr, $($s:stmt),*) => {
        let start = Instant::now();
        $($s;)*
        let duration = start.elapsed();
        info!(
            "{} ({}.{} seconds)",
            $desc,
            duration.as_secs(),
            duration.subsec_millis() / 10
        );
    };
}

impl PrustiServer {
    pub fn new() -> PrustiServer {
        debug!("Prepare verifier builder...");
        run_timed!("JVM startup", let verifier_builder = VerifierBuilder::new());
        PrustiServer { verifier_builder }
    }

    pub fn run_verifier(
        &self,
        program: Program,
        backend: viper::VerificationBackend,
    ) -> viper::VerificationResult {
        run_timed!("Verifier startup",
            let context = self.verifier_builder.new_verification_context(),
            let verifier = context.new_viper_verifier(backend)
        );

        let ast_factory = context.new_ast_factory();
        let viper_program = program.to_viper(&ast_factory);

        // TODO: dump viper program if desired

        verifier.verify(viper_program)
    }
}
