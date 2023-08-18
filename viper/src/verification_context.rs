// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    ast_factory::*, ast_utils::*, verification_backend::VerificationBackend, verifier::Verifier,
};
use jni::AttachGuard;
use log::{debug, info};
use std::{
    env,
    path::{Path, PathBuf},
};

use crate::smt_manager::SmtManager;

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

    /// Should be used only by tests.
    pub fn new_verifier_with_default_smt(&self, backend: VerificationBackend) -> Verifier {
        self.new_verifier_with_default_smt_and_extra_args(backend, vec![])
    }

    /// Should be used only by tests.
    pub fn new_verifier_with_default_smt_and_extra_args(
        &self,
        backend: VerificationBackend,
        extra_args: Vec<String>,
    ) -> Verifier {
        let z3_exe =
            env::var("Z3_EXE").expect("the Z3_EXE environment variable should not be empty");
        let boogie_exe = env::var("BOOGIE_EXE").ok();
        self.new_verifier(
            backend,
            extra_args,
            None,
            z3_exe,
            boogie_exe,
            SmtManager::default(),
        )
    }

    #[tracing::instrument(level = "debug", skip(self, smt_manager))]
    pub fn new_verifier(
        &self,
        backend: VerificationBackend,
        extra_args: Vec<String>,
        report_path: Option<PathBuf>,
        z3_exe: String,
        boogie_exe: Option<String>,
        smt_manager: SmtManager,
    ) -> Verifier {
        let mut verifier_args: Vec<String> = vec![];

        // Set Z3 binary
        info!("Using Z3 exe: '{}'", &z3_exe);
        assert!(
            Path::new(&z3_exe).is_file(),
            "The Z3_EXE environment variable ({z3_exe:?}) does not point to a valid file."
        );
        verifier_args.extend(vec!["--z3Exe".to_string(), z3_exe]);

        // Set Boogie binary
        if let VerificationBackend::Carbon = backend {
            let boogie_exe =
                boogie_exe.expect("the BOOGIE_EXE environment variable should not be empty");
            info!("Using BOOGIE exe: '{}'", &boogie_exe);
            assert!(
                Path::new(&boogie_exe).is_file(),
                "The BOOGIE_EXE environment variable ({boogie_exe:?}) does not point to a valid file."
            );
            verifier_args.extend(vec!["--boogieExe".to_string(), boogie_exe]);
        }

        verifier_args.extend(extra_args);

        debug!("Verifier arguments: '{}'", verifier_args.to_vec().join(" "));

        Verifier::new(&self.env, backend, report_path, smt_manager).initialize(&verifier_args)
    }
}
