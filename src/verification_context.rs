// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use jni::AttachGuard;
use ast_factory::*;
use verifier::Verifier;
use verifier::state;
use ast_utils::*;
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
}
