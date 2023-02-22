use prusti_common::vir::ToViper;
use viper::{AstFactory, VerificationResult};

pub enum Backend<'a> {
    Viper(viper::Verifier<'a>),
}

impl<'a> Backend<'a> {
    pub fn verify(&mut self, program: &prusti_common::vir::program::Program) -> VerificationResult {
        match self {
            Backend::Viper(viper) => {
                let ast_factory = AstFactory::new(viper.env);
                let program =
                    program.to_viper(prusti_common::vir::LoweringContext::default(), &ast_factory);
                viper.verify(program)
            }
        }
    }
}
