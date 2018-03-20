// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Method, Field, VerificationError};
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;
use std::collections::HashMap;
use viper::CfgBlockIndex;
use prusti_interface::environment::BasicBlockIndex;

pub struct ProceduresTable<'a, P: 'a + Procedure> {
    ast_factory: viper::AstFactory<'a>,
    cfg_factory: viper::CfgFactory<'a>,
    env: &'a Environment<ProcedureImpl=P>,
}

impl<'a, P: Procedure> ProceduresTable<'a, P> {
    pub fn new(verification_ctx: &'a viper::VerificationContext<'a>, env: &'a Environment<ProcedureImpl=P>) -> Self {
        ProceduresTable {
            ast_factory: verification_ctx.new_ast_factory(),
            cfg_factory: verification_ctx.new_cfg_factory(),
            env
        }
    }

    pub fn get_definition(&self, proc_def_id: ProcedureDefId) -> Method<'a> {
        let procedure = self.env.get_procedure(proc_def_id);
        let mut cfg = self.cfg_factory.new_cfg_method(
            // method name
            "foo",
            // formal args
            vec![],
            // formal returns
            vec![],
            // local vars
            vec![self.ast_factory.local_var_decl("a", self.ast_factory.int_type())],
        );
        let bbi_to_cfg_block: HashMap<BasicBlockIndex, CfgBlockIndex>;
        procedure.walk_once_cfg(|bbi, bb_data| {
            let block = cfg.add_block(
                // invariants
                vec![],
                // statements
                self.ast_factory.seqn(&vec![], &vec![])
            );
        });
        unimplemented!();
    }
}
