// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::verifier::Verifier as VerifierSpec;
use prusti_interface::verifier::VerificationContext as VerificationContextSpec;
use prusti_interface::verifier::VerifierBuilder as VerifierBuilderSpec;
use prusti_interface::data::VerificationResult;
use prusti_interface::environment::Environment;
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

impl<'a> VerifierBuilderSpec<'a> for VerifierBuilder {
    type VerificationContextImpl = VerificationContext<'a>;

    fn new_verification_context(&'a self) -> VerificationContext<'a> {
        let verification_ctx = self.viper.new_verification_context();
        VerificationContext::new(verification_ctx)
    }
}

pub struct VerificationContext<'a> {
    verification_ctx: viper::VerificationContext<'a>,
}

impl<'a> VerificationContext<'a> {
    pub fn new(verification_ctx: viper::VerificationContext<'a>) -> Self {
        VerificationContext { verification_ctx }
    }
}

impl<'a> VerificationContextSpec<'a> for VerificationContext<'a> {
    type VerifierImpl = Verifier<'a>;

    fn new_verifier(&'a self) -> Verifier<'a> {
        Verifier::new(&self.verification_ctx)
    }
}

pub struct Verifier<'a> {
    verification_ctx: &'a viper::VerificationContext<'a>,
    verifier: viper::Verifier<'a, viper::state::Started>,
    procedures_table: ProceduresTable<'a>,
    fields_table: FieldsTable<'a>,
}

impl<'a> Verifier<'a> {
    pub fn new(
        verification_ctx: &'a viper::VerificationContext<'a>,
    ) -> Self {
        Verifier {
            verification_ctx,
            verifier: verification_ctx.new_verifier(),
            procedures_table: ProceduresTable::new(verification_ctx),
            fields_table: FieldsTable::new(verification_ctx),
        }
    }
}

impl<'a> VerifierSpec for Verifier<'a> {
    fn verify(&mut self, env: &mut Environment, task: &VerificationTask) -> VerificationResult {
        let ast_factory = self.verification_ctx.new_ast_factory();

        // let epoch = env.get_current_epoch();
        let mut verification_methods: Vec<Method> = vec![];
        let mut verification_errors: Vec<VerificationError> = vec![];

        for proc_id in &task.procedures {
            /* TODO: cache old results
            let method_or_result = self.procedures_table.get_use(procedure, epoch);
            match method_or_result {
                Left(method) => verification_methods.push(method),
                Right(errors) => verification_errors.append(errors)
            }
            */
            let method = self.procedures_table.get_definition(*proc_id);
            verification_methods.push(method)
        }
        let verification_fields: Vec<Field> = self.fields_table.get_used_definitions();
        let program = ast_factory.program(&[], &verification_fields, &[], &[], &verification_methods);

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

    fn invalidate_all(&mut self, _env: &mut Environment) {
        // TODO
    }
}
