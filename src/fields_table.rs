// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Method, Field, VerificationError};

pub struct FieldsTable<'a> {
    ast_factory: viper::AstFactory<'a>
}

impl<'a> FieldsTable<'a> {
    pub fn new(verification_ctx: &'a viper::VerificationContext<'a>) -> Self {
        FieldsTable {
            ast_factory: verification_ctx.new_ast_factory(),
        }
    }

    pub fn get_used_definitions(&self) -> Vec<Field<'a>> {
        unimplemented!();
    }
}
