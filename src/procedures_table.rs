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
use rustc::mir::TerminatorKind;
use viper::Successor;

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
        let mut cfg_blocks: HashMap<BasicBlockIndex, CfgBlockIndex> = HashMap::new();

        // Build CFG blocks
        procedure.walk_once_cfg(|bbi, bb_data| {
            let statements = &bb_data.statements;

            let cfg_block = cfg.add_block(
                // invariants
                vec![],
                // statements
                self.ast_factory.seqn(&vec![], &vec![])
            );
            cfg_blocks.insert(bbi, cfg_block);
        });

        let abort_cfg_block = cfg.add_block(
            // invariants
            vec![],
            // statements
            self.ast_factory.seqn(&vec![], &vec![])
        );

        // Build CFG edges
        procedure.walk_once_cfg(|bbi, bb_data| {
            let terminator = &bb_data.terminator;
            let cfg_block = *cfg_blocks.get(&bbi).unwrap();

            if let Some(ref term) = *terminator {
                match term.kind {
                    TerminatorKind::Return => {
                        cfg.set_successor(cfg_block, Successor::Return());
                    }
                    TerminatorKind::Goto { target } => {
                        if let Some(target_cfg_block) = cfg_blocks.get(&target) {
                            cfg.set_successor(cfg_block, Successor::Goto(*target_cfg_block));
                        } else {
                            debug!("Discard edge {:?} -> {:?}", bbi, target)
                        }
                    }
                    TerminatorKind::SwitchInt { ref targets, .. } => {
                        for target in targets {
                            // TODO write_normal_edge(&mut graph, bb, *target);
                        }
                    }
                    TerminatorKind::Resume => {
                        // TODO write_normal_edge_str_target(&mut graph, bb, "Resume");
                    }
                    TerminatorKind::Abort => {
                        // TODO write_normal_edge_str_target(&mut graph, bb, "Abort");
                    }
                    TerminatorKind::Unreachable => {}
                    TerminatorKind::DropAndReplace { ref target, unwind, .. } |
                    TerminatorKind::Drop { ref target, unwind, .. } => {
                        // TODO write_normal_edge(&mut graph, bb, *target);
                        if let Some(target) = unwind {
                            // TODO write_unwind_edge(&mut graph, bb, target);
                        }
                    }

                    TerminatorKind::Call { ref destination, cleanup, .. } => {
                        if let &Some((_, target)) = destination {
                            // TODO write_normal_edge(&mut graph, bb, target);
                        }
                        if let Some(target) = cleanup {
                            // TODO write_unwind_edge(&mut graph, bb, target);
                        }
                    }
                    TerminatorKind::Assert { target, .. } => {
                        // TODO write_normal_edge(&mut graph, bb, target);
                    }
                    TerminatorKind::Yield { .. } => { unimplemented!() }
                    TerminatorKind::GeneratorDrop => { unimplemented!() }
                    TerminatorKind::FalseEdges { ref real_target, ref imaginary_targets } => {
                        // TODO write_normal_edge(&mut graph, bb, *real_target);
                    }
                    TerminatorKind::FalseUnwind { real_target, unwind } => {
                        // TODO write_normal_edge(&mut graph, bb, real_target);
                    }
                };
            }
        });

        unimplemented!();
    }
}
