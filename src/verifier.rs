// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::verifier::Verifier as VerifierSpec;
use prusti_interface::verifier::VerificationContext as VerificationContextSpec;
use prusti_interface::verifier::VerifierBuilder as VerifierBuilderSpec;
use prusti_interface::data::VerificationResult;
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;
use prusti_interface::data::VerificationTask;
use viper::{self, Viper, Method, Field, VerificationError};
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

impl<'v, 'tcx: 'v, P: 'v + Procedure<'tcx>> VerifierBuilderSpec<'v, 'tcx, P> for VerifierBuilder {
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

impl<'v, 'tcx: 'v, P: 'v + Procedure<'tcx>> VerificationContextSpec<'v, 'tcx, P> for VerificationContext<'v> {
    type VerifierImpl = Verifier<'v, 'tcx, P>;

    fn new_verifier(&'v self, env: &'v Environment<'tcx, ProcedureImpl=P>) -> Verifier<'v, 'tcx, P> {
        Verifier::new(
            self.verification_ctx.new_ast_factory(),
            self.verification_ctx.new_cfg_factory(),
            self.verification_ctx.new_verifier(),
            env
        )
    }
}

pub struct Verifier<'v, 'tcx: 'v, P: 'v + Procedure<'tcx>> {
    ast_factory: viper::AstFactory<'v>,
    cfg_factory: viper::CfgFactory<'v>,
    verifier: viper::Verifier<'v, viper::state::Started>,
    env: &'v Environment<'tcx, ProcedureImpl=P>,
    encoder: Encoder<'v, 'tcx, P>
}

impl<'v, 'tcx, P: Procedure<'tcx>> Verifier<'v, 'tcx, P> {
    pub fn new(
        ast_factory: viper::AstFactory<'v>,
        cfg_factory: viper::CfgFactory<'v>,
        verifier: viper::Verifier<'v, viper::state::Started>,
        env: &'v Environment<'tcx, ProcedureImpl=P>,
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

impl<'v, 'tcx, P: 'v + Procedure<'tcx>> VerifierSpec for Verifier<'v, 'tcx, P> {
    fn verify(&mut self, task: &VerificationTask) -> VerificationResult {
        // let epoch = self.env.get_current_epoch();
        let mut verification_errors: Vec<VerificationError> = vec![];

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
