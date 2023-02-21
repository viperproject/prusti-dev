use crate::dump_viper_program;
use prusti_common::{
    config,
    vir::{LoweringContext, ToViper},
    Stopwatch,
};
use viper::{VerificationContext, VerificationResult};

pub enum Backend<'a> {
    Viper(viper::Verifier<'a>, &'a VerificationContext<'a>),
    Lithium(native_verifier::Verifier),
}

impl<'a> Backend<'a> {
    pub fn verify(&mut self, program: &prusti_common::vir::program::Program) -> VerificationResult {
        match self {
            Backend::Viper(viper, context) => {
                let mut stopwatch =
                    Stopwatch::start("prusti-server backend", "construction of JVM objects");

                let ast_utils = context.new_ast_utils();

                ast_utils.with_local_frame(16, || {
                    let ast_factory = context.new_ast_factory();
                    let viper_program = program.to_viper(LoweringContext::default(), &ast_factory);

                    if config::dump_viper_program() {
                        stopwatch.start_next("dumping viper program");
                        dump_viper_program(
                            &ast_utils,
                            viper_program,
                            &program.get_name_with_check_mode(),
                        );
                    }

                    stopwatch.start_next("viper verification");
                    viper.verify(viper_program)
                })
            }
            Backend::Lithium(lithium) => lithium.verify(program),
        }
    }
}
