// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use ast_factory::*;
use ast_utils::*;
use jni::AttachGuard;
use std::env;
use std::path::{Path, PathBuf};
use verification_backend::VerificationBackend;
use verifier::state;
use verifier::Verifier;

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

    pub fn new_verifier(&self, backend: VerificationBackend, log_path: PathBuf) -> Verifier<state::Started> {
        self.new_verifier_with_args(backend, vec![], log_path)
    }

    pub fn new_verifier_with_args(
        &self,
        backend: VerificationBackend,
        extra_args: Vec<String>,
        log_path: PathBuf,
    ) -> Verifier<state::Started> {
        let mut verifier_args: Vec<String> = vec![];

        // Set Z3 binary
        let z3_path = vec![
            env::var("Z3_PATH").ok(),
            env::var("Z3_EXE").ok(),
            Some("z3".to_string()),
        ]
        .into_iter()
        .flatten()
        .find(|path| Path::new(path).exists())
        .expect("No valid Z3 path has been found. Please set Z3_EXE.");
        info!("Using Z3 path: '{}'", &z3_path);
        verifier_args.extend(vec!["--z3Exe".to_string(), z3_path]);

        // Set Boogie binary
        if let VerificationBackend::Carbon = backend {
            let boogie_path = vec![
                env::var("BOOGIE_PATH").ok(),
                env::var("BOOGIE_EXE").ok(),
                Some("boogie".to_string()),
            ]
            .into_iter()
            .flatten()
            .find(|path| Path::new(path).exists())
            .expect("No valid Boogie path has been found. Please set BOOGIE_EXE.");
            info!("Using BOOGIE path: '{}'", &boogie_path);
            verifier_args.extend(vec!["--boogieExe".to_string(), boogie_path]);
        }

        verifier_args.extend(extra_args);
        verifier_args.push("dummy-program.sil".to_string());

        debug!(
            "Verifier arguments: '{}'",
            verifier_args.iter().cloned().collect::<Vec<_>>().join(" ")
        );

        Verifier::<state::Uninitialized>::new(&self.env, backend, log_path)
            .parse_command_line(&verifier_args)
            .start()
    }
}
