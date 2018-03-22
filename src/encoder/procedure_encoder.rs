// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Stmt, Expr, VerificationError};
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
use encoder::Encoder;
use encoder::borrows::compute_borrow_infos;

pub struct ProcedureEncoder<'p, 'v: 'p, 'tcx: 'v, P: 'v + Procedure<'tcx>> {
    encoder: &'p mut Encoder<'v, 'tcx, P>,
    proc_def_id: ProcedureDefId,
    procedure: &'p P,
    mir: &'p mir::Mir<'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v, P: 'v + Procedure<'tcx>> ProcedureEncoder<'p, 'v, 'tcx, P> {
    pub fn new(encoder: &'p mut Encoder<'v, 'tcx, P>, procedure: &'p P) -> Self {
        ProcedureEncoder {
            encoder,
            proc_def_id: procedure.get_id(),
            procedure,
            mir: procedure.get_mir()
        }
    }

    fn encode_local(&self, local: mir::Local) -> viper::LocalVarDecl<'v> {
        trace!("Encode local {:?}", self.encode_local_var_name(local));
        self.encoder.ast_factory.local_var_decl(
            &self.encode_local_var_name(local),
            self.encoder.encode_type(self.get_rust_local_ty(local))
        )
    }

    fn encode_formal_args_decl(&self) -> Vec<viper::LocalVarDecl<'v>> {
        self.mir.args_iter().map(|x| self.encode_local(x)).collect()
    }

    fn encode_formal_returns_decl(&self) -> Vec<viper::LocalVarDecl<'v>> {
        self.mir.local_decls.indices().take(1).map(|x| self.encode_local(x)).collect()
    }

    fn encode_local_vars_decl(&self) -> Vec<viper::LocalVarDecl<'v>> {
        self.mir.vars_and_temps_iter().filter(
            |l| !self.get_rust_local_ty(*l).is_never()
        ).map(|x| self.encode_local(x)).collect()
    }

    fn encode_statement(&self, stmt: &mir::Statement) -> Stmt {
        debug!("Encode statement '{:?}'", stmt);
        // TODO!
        self.encoder.ast_factory.seqn(&[], &[])
    }

    fn encode_terminator(&self, term: &mir::Terminator) -> Stmt {
        debug!("Encode terminator '{:?}'", term);
        match term.kind {
            x => unimplemented!("{:?}", x)
        }
    }

    pub fn set_used(&mut self) {
        compute_borrow_infos(self.procedure);
        let ast = self.encoder.ast_factory;
        let mut cfg = self.encoder.cfg_factory.new_cfg_method(
            // method name
            self.encode_procedure_name(),
            // formal args
            self.encode_formal_args_decl(),
            // formal returns
            self.encode_formal_returns_decl(),
            // local vars
            self.encode_local_vars_decl()
        );
        let mut cfg_blocks: HashMap<BasicBlockIndex, CfgBlockIndex> = HashMap::new();

        // Build CFG blocks
        self.procedure.walk_once_cfg(|bbi, bb_data| {
            let statements: &Vec<mir::Statement<'tcx>> = &bb_data.statements;
            let mut viper_statements: Vec<Stmt> = vec![];

            // Encode statements
            for (stmt_index, stmt) in statements.iter().enumerate() {
                debug!("Encode statement {:?}:{}", bbi, stmt_index);
                viper_statements.push(self.encode_statement(stmt))
            }

            // Encode effect of terminator (assert, function call, ...)
            if let Some(ref term) = bb_data.terminator {
                viper_statements.push(self.encode_terminator(term));
            }

            let cfg_block = cfg.add_block(
                // label
                &format!("{:?}", bbi),
                // invariants
                vec![],
                // statements
                ast.seqn(
                    &viper_statements,
                    &vec![]
                )
            );
            cfg_blocks.insert(bbi, cfg_block);
        });

        let spec_cfg_block = cfg.add_block(
            // label
            "spec",
            // invariants
            vec![],
            // statements
            ast.seqn(&[], &[])
        );
        cfg.set_successor(spec_cfg_block, Successor::Unreachable);

        let abort_cfg_block = cfg.add_block(
            // label
            "abort",
            // invariants
            vec![],
            // statements
            ast.seqn(&vec![], &vec![])
        );
        cfg.set_successor(abort_cfg_block, Successor::Unreachable);

        // Build CFG edges
        self.procedure.walk_once_cfg(|bbi, bb_data| {
            let terminator = &bb_data.terminator;
            let cfg_block = *cfg_blocks.get(&bbi).unwrap();

            if let Some(ref term) = *terminator {
                let successor = match term.kind {
                    TerminatorKind::Return => Successor::Return,

                    TerminatorKind::Goto { target } => {
                        let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                        Successor::Goto(*target_cfg_block)
                    },

                    TerminatorKind::SwitchInt { ref targets, ref discr, ref values, switch_ty } => {
                        trace!("SwitchInt ty '{:?}', discr '{:?}', values '{:?}'", switch_ty, discr, values);
                        let mut cfg_targets: Vec<(Expr, CfgBlockIndex)> = vec![];
                        for (i, value) in values.iter().enumerate() {
                            let target = targets[i as usize];
                            // Convert int to bool, if required
                            let viper_value = if (switch_ty.sty == ty::TypeVariants::TyBool) {
                                let viper_num_value = self.encoder.encode_const_int(value);
                                ast.not(ast.eq_cmp(viper_num_value, ast.int_lit(0)))
                            } else {
                                self.encoder.encode_const_int(value)
                            };
                            let viper_guard = ast.eq_cmp(
                                self.encode_operand_eval(discr),
                                viper_value
                            );
                            let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                            cfg_targets.push((viper_guard, *target_cfg_block))
                        }
                        let default_target = targets[values.len()];
                        let cfg_default_target = cfg_blocks.get(&default_target).unwrap_or(&spec_cfg_block);
                        Successor::GotoSwitch(cfg_targets, *cfg_default_target)
                    },

                    TerminatorKind::Resume => unimplemented!(),

                    TerminatorKind::Unreachable => Successor::Unreachable,

                    TerminatorKind::Abort => Successor::Goto(abort_cfg_block),

                    TerminatorKind::DropAndReplace { ref target, unwind, .. } |
                    TerminatorKind::Drop { ref target, unwind, .. } => {
                        let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                        Successor::Goto(*target_cfg_block)
                    },

                    TerminatorKind::Call { ref destination, cleanup, .. } => {
                        if let &Some((_, target)) = destination {
                            let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                            Successor::Goto(*target_cfg_block)
                        } else {
                            Successor::Unreachable
                        }
                    },

                    TerminatorKind::Assert { target, .. } => {
                        let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                        Successor::Goto(*target_cfg_block)
                    },

                    TerminatorKind::Yield { .. } => unimplemented!(),

                    TerminatorKind::GeneratorDrop => unimplemented!(),

                    TerminatorKind::FalseEdges { ref real_target, ref imaginary_targets } => {
                        let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                        Successor::Goto(*target_cfg_block)
                    },

                    TerminatorKind::FalseUnwind { real_target, unwind } => {
                        let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                        Successor::Goto(*target_cfg_block)
                    }
                };
                cfg.set_successor(cfg_block, successor);
            }
        });

        let method = cfg.to_ast().ok().unwrap();
        self.encoder.procedures.insert(self.proc_def_id, method);
    }

    fn get_rust_local_decl(&self, local: mir::Local) -> &mir::LocalDecl<'tcx> {
        &self.mir.local_decls[local]
    }

    fn get_rust_local_ty(&self, local: mir::Local) -> &ty::Ty<'tcx> {
        &self.get_rust_local_decl(local).ty
    }

    fn encode_local_var_name(&self, local: mir::Local) -> String {
        let local_decl = self.get_rust_local_decl(local);
        match local_decl.name {
            Some(ref name) => format!("{:?}", name),
            None => format!("{:?}", local)
        }
    }

    fn encode_place_eval(&self, place: &mir::Place<'tcx>) -> Expr<'v> {
        match place {
            &mir::Place::Local(local) => {
                let var_name = self.encode_local_var_name(local);
                let var_type = self.encoder.ast_factory.ref_type();
                self.encoder.ast_factory.local_var(&var_name, var_type)
            }
            x => unimplemented!("{:?}", x),
        }
    }

    fn encode_operand_eval(&self, operand: &mir::Operand<'tcx>) -> Expr<'v> {
        match operand {
            &mir::Operand::Copy(ref place) |
            &mir::Operand::Move(ref place) => self.encode_place_eval(place),
            &mir::Operand::Constant(box mir::Constant{ literal: mir::Literal::Value{ value: &ty::Const{ ref val, .. } }, ..}) =>
                self.encoder.encode_const_val(val),
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_procedure_name(&self) -> String {
        self.procedure.get_name()
    }
}
