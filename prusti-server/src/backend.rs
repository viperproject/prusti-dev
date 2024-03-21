use crate::dump_viper_program;
use prusti_utils::{
    config,
    Stopwatch,
};
use viper::{VerificationContext, VerificationResult};

pub enum Backend<'a> {
    Viper(viper::Verifier<'a>, &'a VerificationContext<'a>),
}

impl<'a> Backend<'a> {
    pub fn verify(&mut self, program: vir::ProgramRef) -> VerificationResult {
        match self {
            Backend::Viper(viper, context) => {
                let mut stopwatch =
                    Stopwatch::start("prusti-server backend", "construction of JVM objects");

                let ast_utils = context.new_ast_utils();

                ast_utils.with_local_frame(16, || {
                    let ast_factory = context.new_ast_factory();

                    let viper_program = vir::with_vcx(|vcx| {
                        let program = vcx.get_program(program);
                        prusti_viper::program_to_viper(program, &ast_factory)
                    });

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
        }
    }
}
