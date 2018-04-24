// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::verifier::Verifier as VerifierSpec;
use prusti_interface::verifier::VerificationContext as VerificationContextSpec;
use prusti_interface::verifier::VerifierBuilder as VerifierBuilderSpec;
use prusti_interface::data::VerificationResult;
use prusti_interface::environment::EnvironmentImpl;
use prusti_interface::data::VerificationTask;
use viper::{self, Viper};
use encoder::Encoder;

pub struct VerifierBuilder {
    viper: Viper,
}

impl VerifierBuilder {
    pub fn new() -> Self {
        VerifierBuilder {
            viper: Viper::new(),
        }
    }
}

impl Default for VerifierBuilder {
    fn default() -> Self {
        VerifierBuilder::new()
    }
}

impl<'v, 'r, 'a, 'tcx> VerifierBuilderSpec<'v, 'r, 'a, 'tcx> for VerifierBuilder
    where
        'r: 'v,
        'a: 'r,
        'tcx: 'a
{
    type VerificationContextImpl = VerificationContext<'v>;

    fn new_verification_context(&'v self) -> VerificationContext<'v> {
        let verification_ctx = self.viper.new_verification_context();
        VerificationContext::new(verification_ctx)
    }
}

pub struct VerificationContext<'v> {
    verification_ctx: viper::VerificationContext<'v>
}

impl<'v> VerificationContext<'v> {
    pub fn new(verification_ctx: viper::VerificationContext<'v>) -> Self {
        VerificationContext { verification_ctx }
    }
}

impl<'v, 'r, 'a, 'tcx> VerificationContextSpec<'v, 'r, 'a, 'tcx> for VerificationContext<'v>
    where
        'r: 'v,
        'a: 'r,
        'tcx: 'a
{
    type VerifierImpl = Verifier<'v, 'r, 'a, 'tcx>;

    fn new_verifier(&'v self, env: &'v EnvironmentImpl<'r, 'a, 'tcx>) -> Verifier<'v, 'r, 'a, 'tcx> {
        Verifier::new(
            self.verification_ctx.new_ast_factory(),
            self.verification_ctx.new_cfg_factory(),
            self.verification_ctx.new_verifier(),
            env
        )
    }
}

pub struct Verifier<'v, 'r, 'a, 'tcx>
    where
        'r: 'v,
        'a: 'r,
        'tcx: 'a
{
    ast_factory: viper::AstFactory<'v>,
    cfg_factory: viper::CfgFactory<'v>,
    verifier: viper::Verifier<'v, viper::state::Started>,
    env: &'v EnvironmentImpl<'r, 'a, 'tcx>,
    encoder: Encoder<'v, 'r, 'a, 'tcx>,
}

impl<'v, 'r, 'a, 'tcx> Verifier<'v, 'r, 'a, 'tcx> {
    pub fn new(
        ast_factory: viper::AstFactory<'v>,
        cfg_factory: viper::CfgFactory<'v>,
        verifier: viper::Verifier<'v, viper::state::Started>,
        env: &'v EnvironmentImpl<'r, 'a, 'tcx>,
    ) -> Self {
        Verifier {
            ast_factory,
            cfg_factory,
            verifier,
            env,
            encoder: Encoder::new(ast_factory, cfg_factory, env)
        }
    }
}

impl<'v, 'r, 'a, 'tcx> VerifierSpec for Verifier<'v, 'r, 'a, 'tcx> {
    fn verify(&mut self, task: &VerificationTask) -> VerificationResult {
        for proc_id in &task.procedures {
            let _ = self.encoder.encode_procedure(*proc_id);
        }

        let program = self.ast_factory.program(
            &self.encoder.get_used_viper_domains(),
            &self.encoder.get_used_viper_fields(),
            &self.encoder.get_used_viper_functions(),
            &self.encoder.get_used_viper_predicates(),
            &self.encoder.get_used_viper_methods()
        );

        let verification_result: viper::VerificationResult = self.verifier.verify(program);

        let verification_errors = if let viper::VerificationResult::Failure(mut errors) = verification_result {
            errors
        } else {
            vec![]
        };

        if verification_errors.is_empty() {
            VerificationResult::Success
        } else {
            for error in verification_errors {
                debug!("Verification error: {:?}", error);
                // TODO: emit errors using env?
            }
            VerificationResult::Failure
        }
    }

    fn invalidate_all(&mut self) {
        unimplemented!()
    }
}
