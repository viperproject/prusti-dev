// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Expr, VerificationError};
use viper::{Domain, Field, Function, Predicate, Method};
use viper::AstFactory;
use rustc::mir;
use rustc::ty;
use prusti_interface::environment::Procedure;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Environment;
use std::collections::HashMap;
use viper::CfgBlockIndex;
use prusti_interface::environment::BasicBlockIndex;
use rustc::mir::TerminatorKind;
use viper::Successor;
use rustc::middle::const_val::{ConstInt, ConstVal};

pub struct ViperEncoder<'v, P: 'v + Procedure> {
    ast_factory: viper::AstFactory<'v>,
    cfg_factory: viper::CfgFactory<'v>,
    env: &'v Environment<ProcedureImpl=P>,
    procedures: HashMap<ProcedureDefId, Method<'v>>,
}

impl<'v, P: Procedure> ViperEncoder<'v, P> {
    pub fn new(ast_factory: viper::AstFactory<'v>,
               cfg_factory: viper::CfgFactory<'v>,
               env: &'v Environment<ProcedureImpl=P>) -> Self {
        ViperEncoder {
            ast_factory,
            cfg_factory,
            env,
            procedures: HashMap::new()
        }
    }

    pub fn get_used_viper_domains(&self) -> Vec<Domain<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_fields(&self) -> Vec<Field<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_functions(&self) -> Vec<Function<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_predicates(&self) -> Vec<Predicate<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_methods(&self) -> Vec<Method<'v>> {
        // TODO
        vec![]
    }

    pub fn use_rust_procedure(&mut self, proc_def_id: ProcedureDefId) {
        let ast = self.ast_factory;
        let procedure = self.env.get_procedure(proc_def_id);
        let mut cfg = self.cfg_factory.new_cfg_method(
            // method name
            self.encode_procedure_name(&procedure),
            // formal args
            vec![],
            // formal returns
            vec![],
            // local vars
            vec![ast.local_var_decl("a", ast.int_type())],
        );
        let mut cfg_blocks: HashMap<BasicBlockIndex, CfgBlockIndex> = HashMap::new();

        // Build CFG blocks
        procedure.walk_once_cfg(|bbi, bb_data| {
            let statements = &bb_data.statements;

            let cfg_block = cfg.add_block(
                // label
                &format!("{:?}", bbi),
                // invariants
                vec![],
                // statements
                ast.seqn(&vec![], &vec![])
            );
            cfg_blocks.insert(bbi, cfg_block);
        });

        let spec_cfg_block = cfg.add_block(
            // label
            "spec",
            // invariants
            vec![],
            // statements
            ast.seqn(&vec![
                ast.assert_with_comment(
                    ast.false_lit(),
                    ast.no_position(),
                    "This should never be reached: "
                )
            ], &vec![])
        );

        let abort_cfg_block = cfg.add_block(
            // label
            "abort",
            // invariants
            vec![],
            // statements
            ast.seqn(&vec![
                ast.assert_with_comment(
                    ast.false_lit(),
                    ast.no_position(),
                    "Abort block: "
                )
            ], &vec![])
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
                        let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                        cfg.set_successor(cfg_block, Successor::Goto(*target_cfg_block));
                    }
                    TerminatorKind::SwitchInt { ref targets, ref discr, ref values, .. } => {
                        let mut cfg_targets: Vec<(Expr, CfgBlockIndex)> = vec![];
                        for (i, value) in values.iter().enumerate() {
                            let target = targets[i as usize];
                            if let ConstInt::U8(value) = *value {
                                let viper_guard = ast.eq_cmp(
                                    self.encode_operand_eval(discr),
                                    ast.int_lit(value as i32)
                                );
                                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                                cfg_targets.push((viper_guard, *target_cfg_block))
                            } else {
                                debug!("Skip value {:?} at SwitchInt of {:?}", value, bbi)
                            }
                        }
                        let default_target = targets[values.len()];
                        let cfg_default_target = cfg_blocks.get(&default_target).unwrap_or(&spec_cfg_block);
                        cfg.set_successor(cfg_block, Successor::GotoSwitch(cfg_targets, *cfg_default_target));
                    }
                    TerminatorKind::Resume => { }
                    TerminatorKind::Abort => {
                        cfg.set_successor(cfg_block, Successor::Goto(abort_cfg_block));
                    }
                    TerminatorKind::Unreachable => {}
                    TerminatorKind::DropAndReplace { ref target, unwind, .. } |
                    TerminatorKind::Drop { ref target, unwind, .. } => {
                        let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                        cfg.set_successor(cfg_block, Successor::Goto(*target_cfg_block));
                    }

                    TerminatorKind::Call { ref destination, cleanup, .. } => {
                        if let &Some((_, target)) = destination {
                            let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                            cfg.set_successor(cfg_block, Successor::Goto(*target_cfg_block));
                        }
                    }
                    TerminatorKind::Assert { target, .. } => {
                        let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                        cfg.set_successor(cfg_block, Successor::Goto(*target_cfg_block));
                    }
                    TerminatorKind::Yield { .. } => { unimplemented!() }
                    TerminatorKind::GeneratorDrop => { unimplemented!() }
                    TerminatorKind::FalseEdges { ref real_target, ref imaginary_targets } => {
                        let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                        cfg.set_successor(cfg_block, Successor::Goto(*target_cfg_block));
                    }
                    TerminatorKind::FalseUnwind { real_target, unwind } => {
                        let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                        cfg.set_successor(cfg_block, Successor::Goto(*target_cfg_block));
                    }
                };
            }
        });

        let method = cfg.to_ast().ok().unwrap();
        self.procedures.insert(proc_def_id, method);
    }

    fn encode_const_int(&self, const_int: &ConstInt) -> Expr<'v> {
        match const_int {
            &ConstInt::U8(ref val) => self.ast_factory.int_lit_from_ref(val),
            _ => unimplemented!(),
        }
    }

    fn encode_bool(&self, val: bool) -> Expr<'v> {
        if val {
            self.ast_factory.true_lit()
        } else {
            self.ast_factory.false_lit()
        }
    }

    fn encode_const_val<'tcx>(&self, const_val: &ConstVal<'tcx>) -> Expr<'v> {
        match const_val {
            &ConstVal::Integral(ref const_int) => self.encode_const_int(const_int),
            &ConstVal::Bool(val) => self.encode_bool(val),
            _ => unimplemented!()
        }
    }

    fn encode_place_eval<'tcx>(&self,place: &mir::Place<'tcx>) -> Expr<'v> {
        match place {
            &mir::Place::Local(ref local) => {
                let var_name = format!("{:?}", local);
                let var_type = self.ast_factory.int_type(); // FIXME
                self.ast_factory.local_var(&var_name, var_type)
            }
            _ => unimplemented!(),
        }
    }

    fn encode_operand_eval<'tcx>(&self, operand: &mir::Operand<'tcx>) -> Expr<'v> {
        match operand {
            &mir::Operand::Copy(ref place) |
            &mir::Operand::Move(ref place) => self.encode_place_eval(place),
            &mir::Operand::Constant(box mir::Constant{ literal: mir::Literal::Value{ value: &ty::Const{ ref val, .. } }, ..}) =>
                self.encode_const_val(val),
            _ => unimplemented!()
        }
    }

    fn encode_procedure_name(&self, procedure: &P) -> String {
        format!("_{}", procedure.get_name())
    }
}
