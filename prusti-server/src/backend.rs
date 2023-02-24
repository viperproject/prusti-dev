use prusti_common::{
    vir::{LoweringContext, ToViper},
    Stopwatch,
};
use viper::{VerificationContext, VerificationResult};

pub enum Backend<'a> {
    Viper(viper::Verifier<'a>, &'a VerificationContext<'a>),
}

impl<'a> Backend<'a> {
    pub fn verify(&mut self, program: &prusti_common::vir::program::Program) -> VerificationResult {
        match self {
            Backend::Viper(viper, context) => {
                let mut stopwatch = Stopwatch::start("prusti-server backend", "construction of JVM objects");

                let ast_factory = context.new_ast_factory();
                let viper_program = program.to_viper(LoweringContext::default(), &ast_factory);

                context.new_ast_utils().with_local_frame(16, || {
                    stopwatch.start_next("verification");
                    viper.verify(viper_program)
                })
            }
        }
    }
}
