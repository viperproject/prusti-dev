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
use procedures_table::ProceduresTable;
use fields_table::FieldsTable;

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

impl<'v, P: 'v + Procedure> VerifierBuilderSpec<'v, P> for VerifierBuilder {
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

impl<'v, P: 'v + Procedure> VerificationContextSpec<'v, P> for VerificationContext<'v> {
    type VerifierImpl = Verifier<'v, P>;

    fn new_verifier(&'v self, env: &'v Environment<ProcedureImpl=P>) -> Verifier<'v, P> {
        Verifier::new(
            self.verification_ctx.new_ast_factory(),
            self.verification_ctx.new_cfg_factory(),
            self.verification_ctx.new_verifier(),
            env
        )
    }
}

pub struct Verifier<'v, P: 'v + Procedure> {
    ast_factory: viper::AstFactory<'v>,
    cfg_factory: viper::CfgFactory<'v>,
    verifier: viper::Verifier<'v, viper::state::Started>,
    env: &'v Environment<ProcedureImpl=P>,
    procedures_table: ProceduresTable<'v, P>,
    fields_table: FieldsTable<'v, P>,
}

impl<'v, P: Procedure> Verifier<'v, P> {
    pub fn new(
        ast_factory: viper::AstFactory<'v>,
        cfg_factory: viper::CfgFactory<'v>,
        verifier: viper::Verifier<'v, viper::state::Started>,
        env: &'v Environment<ProcedureImpl=P>,
    ) -> Self {
        Verifier {
            ast_factory,
            cfg_factory,
            verifier,
            env,
            procedures_table: ProceduresTable::new(ast_factory, cfg_factory, env),
            fields_table: FieldsTable::new(ast_factory, env),
        }
    }
}

impl<'v, P: 'v + Procedure> VerifierSpec for Verifier<'v, P> {
    fn verify(&mut self, task: &VerificationTask) -> VerificationResult {
        // let epoch = self.env.get_current_epoch();
        let mut verification_errors: Vec<VerificationError> = vec![];

        for proc_id in &task.procedures {
            self.procedures_table.set_used(*proc_id);
        }

        let verification_fields: Vec<Field> = self.fields_table.get_used_definitions();
        let verification_methods: Vec<Method> = self.procedures_table.get_used_definitions();

        let program = self.ast_factory.program(&[], &verification_fields, &[], &[], &verification_methods);

        let verification_result: viper::VerificationResult = self.verifier.verify(program);
        if let viper::VerificationResult::Failure(mut errors) = verification_result {
            // TODO: register errors in corresponding self.procedures_table
            verification_errors.append(&mut errors)
        }

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
        // TODO
    }
}
