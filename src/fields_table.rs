// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Method, Field, VerificationError};
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;

pub struct FieldsTable<'v, P: 'v + Procedure> {
    ast_factory: viper::AstFactory<'v>,
    env: &'v Environment<ProcedureImpl=P>,
}

impl<'v, P: Procedure> FieldsTable<'v, P> {
    pub fn new(ast_factory: viper::AstFactory<'v>, env: &'v Environment<ProcedureImpl=P>) -> Self {
        FieldsTable {
            ast_factory,
            env
        }
    }

    // pub fn get_use(&self) { .. }

    pub fn get_used_definitions(&self) -> Vec<Field<'v>> {
        vec![]
    }
}
