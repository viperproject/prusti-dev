// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Method, Field, VerificationError};
use prusti_interface::data::ProcedureDefId;

pub struct ProceduresTable<'a> {
    ast_factory: viper::AstFactory<'a>
}

impl<'a> ProceduresTable<'a> {
    pub fn new(verification_ctx: &'a viper::VerificationContext<'a>) -> Self {
        ProceduresTable {
            ast_factory: verification_ctx.new_ast_factory(),
        }
    }

    pub fn get_definition(&self, procedure: ProcedureDefId) -> Method<'a> {
        unimplemented!();
    }
}
