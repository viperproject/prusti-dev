extern crate viper_sys;
extern crate jni;

use jni::AttachGuard;
use ast_factory::*;
use error_manager::ErrorManager;
use verifier::Verifier;
use verifier::state;

pub struct VerificationContext<'a> {
    env: AttachGuard<'a>,
}

impl<'a> VerificationContext<'a> {
    pub fn new(env_guard: AttachGuard<'a>) -> Self {
        VerificationContext { env: env_guard }
    }

    pub fn new_ast_factory(&self) -> AstFactory {
        AstFactory::new(&self.env)
    }

    pub fn new_error_manager(&self) -> ErrorManager {
        ErrorManager::default()
    }

    pub fn new_verifier(&self) -> Verifier<state::Started> {
        Verifier::<state::Uninitialized>::new(&self.env)
            .parse_command_line(vec!["--z3Exe", "/usr/bin/viper-z3", "dummy-program.sil"])
            .start()
    }
}
