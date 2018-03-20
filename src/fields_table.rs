// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Method, Field, VerificationError};
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;

pub struct FieldsTable<'a, P: 'a + Procedure> {
    ast_factory: viper::AstFactory<'a>,
    env: &'a Environment<ProcedureImpl=P>,
}

impl<'a, P: Procedure> FieldsTable<'a, P> {
    pub fn new(verification_ctx: &'a viper::VerificationContext<'a>, env: &'a Environment<ProcedureImpl=P>) -> Self {
        FieldsTable {
            ast_factory: verification_ctx.new_ast_factory(),
            env
        }
    }

    pub fn get_used_definitions(&self) -> Vec<Field<'a>> {
        unimplemented!();
    }
}
