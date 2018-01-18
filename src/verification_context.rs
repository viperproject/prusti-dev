use jni::AttachGuard;
use ast_factory::*;
use verifier::Verifier;
use verifier::state;
use ast_utils::*;
use cfg_method::*;
use std::env;

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

    pub fn new_ast_utils(&self) -> AstUtils {
        AstUtils::new(&self.env)
    }

    pub fn new_verifier(&self) -> Verifier<state::Started> {
        let z3_path = env::var("Z3_PATH").unwrap_or_else(|_| "/usr/bin/viper-z3".to_string());

        debug!("Using Z3 path: '{}'", &z3_path);

        Verifier::<state::Uninitialized>::new(&self.env)
            .parse_command_line(&["--z3Exe", &z3_path, "dummy-program.sil"])
            .start()
    }

    pub fn new_cfg_method<IntoString>(
        &self,
        ast_factory: &'a AstFactory,
        method_name: IntoString,
        formal_args: Vec<LocalVarDecl<'a>>,
        formal_returns: Vec<LocalVarDecl<'a>>,
        local_vars: Vec<LocalVarDecl<'a>>,
    ) -> CfgMethod
    where
        IntoString: Into<String>,
    {
        CfgMethod::new(
            ast_factory,
            method_name.into(),
            formal_args,
            formal_returns,
            local_vars,
        )
    }
}
