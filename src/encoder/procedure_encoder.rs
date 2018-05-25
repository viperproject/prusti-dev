// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::mir;
use rustc::ty;
use prusti_interface::environment::ProcedureImpl;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;
use std::collections::HashMap;
use prusti_interface::environment::BasicBlockIndex;
use rustc::mir::TerminatorKind;
use rustc::middle::const_val::ConstVal;
use encoder::Encoder;
use encoder::borrows::ProcedureContract;
use rustc_data_structures::indexed_vec::Idx;
use encoder::places::{Local, LocalVariableManager, Place};
use encoder::loop_encoder::LoopEncoder;
use encoder::vir::{self, Successor, CfgBlockIndex};
use encoder::vir::utils::ExprIterator;
use encoder::foldunfold;
use report::Log;

static PRECONDITION_LABEL: &'static str = "pre";

pub struct ProcedureEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: ProcedureDefId,
    procedure: &'p ProcedureImpl<'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    cfg_method: vir::CfgMethod,
    locals: LocalVariableManager<'tcx>,
    loops: LoopEncoder<'tcx>,
    //dataflow_info: DataflowInfo<'tcx>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> ProcedureEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, procedure: &'p ProcedureImpl<'a, 'tcx>) -> Self {
        let cfg_method = vir::CfgMethod::new(
            // method name
            encoder.encode_procedure_name(procedure.get_id()),
            // formal args
            vec![],
            // formal returns
            vec![],
            // local vars
            vec![],
        );

        let mir = procedure.get_mir();
        let locals = LocalVariableManager::new(&mir.local_decls);
        let loops = LoopEncoder::new(mir);
        // let dataflow_info = procedure.construct_dataflow_info();

        ProcedureEncoder {
            encoder,
            proc_def_id: procedure.get_id(),
            procedure,
            mir: mir,
            cfg_method,
            locals: locals,
            loops: loops,
            //dataflow_info: dataflow_info,
        }
    }

    fn encode_statement(&mut self, stmt: &mir::Statement<'tcx>) -> Vec<vir::Stmt> {
        debug!("Encode statement '{:?}'", stmt);
        let mut stmts: Vec<vir::Stmt> = vec![];

        match stmt.kind {
            mir::StatementKind::StorageDead(_) |
            mir::StatementKind::StorageLive(_) |
            mir::StatementKind::EndRegion(_) => stmts,

            mir::StatementKind::Assign(ref lhs, ref rhs) => {
                let (encoded_lhs, ty, _) = self.encode_place(lhs);
                let type_name = self.encoder.encode_type_predicate_use(ty);
                // Obtain lhs
                if !encoded_lhs.is_base() {
                    stmts.push(
                        vir::Stmt::obtain_acc(encoded_lhs.clone())
                    );
                }
                // Havoc lhs
                stmts.extend(
                    self.encode_havoc(encoded_lhs.clone())
                );
                match rhs {
                    &mir::Rvalue::Use(ref operand) => {
                        let (_, encoded_value, effects_before, effects_after) = self.encode_operand(operand);
                        stmts.extend(effects_before);
                        stmts.push(
                            vir::Stmt::Assign(encoded_lhs, encoded_value.into())
                        );
                        stmts.extend(effects_after);
                        stmts
                    },

                    &mir::Rvalue::BinaryOp(op, ref left, ref right) => {
                        let (encoded_left, effects_before_left, effects_after_left) = self.eval_operand(left);
                        let (encoded_right, effects_before_right, effects_after_right) = self.eval_operand(right);
                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.encode_bin_op_value(op, encoded_left, encoded_right);
                        stmts.extend(effects_before_left);
                        stmts.extend(effects_before_right);
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.access(field),
                                encoded_value
                            )
                        );
                        stmts.extend(effects_after_left);
                        stmts.extend(effects_after_right);
                        stmts
                    },

                    &mir::Rvalue::CheckedBinaryOp(op, ref left, ref right) => {
                        let (encoded_left, effects_before_left, effects_after_left) = self.eval_operand(left);
                        let (encoded_right, effects_before_right, effects_after_right) = self.eval_operand(right);
                        let encoded_value = self.encode_bin_op_value(op, encoded_left.clone(), encoded_right.clone());
                        let encoded_check = self.encode_bin_op_check(op, encoded_left, encoded_right);
                        let field_types = if let ty::TypeVariants::TyTuple(ref x) = ty.sty { x } else { unreachable!() };
                        let value_field = self.encoder.encode_ref_field("tuple_0", field_types[0]);
                        let value_field_value = self.encoder.encode_value_field(field_types[0]);
                        let check_field = self.encoder.encode_ref_field("tuple_1", field_types[1]);
                        let check_field_value = self.encoder.encode_value_field(field_types[1]);
                        stmts.extend(effects_before_left);
                        stmts.extend(effects_before_right);
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.clone()
                                    .access(value_field)
                                    .access(value_field_value),
                                encoded_value,
                            )
                        );
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs
                                    .access(check_field)
                                    .access(check_field_value),
                                encoded_check,
                            )
                        );
                        stmts.extend(effects_after_left);
                        stmts.extend(effects_after_right);
                        stmts
                    },

                    &mir::Rvalue::UnaryOp(op, ref operand)  => {
                        let (encoded_operand, effects_before, effects_after) = self.eval_operand(operand);
                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.encode_unary_op_value(op, encoded_operand);
                        stmts.extend(effects_before);
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.access(field),
                                encoded_value
                            )
                        );
                        stmts.extend(effects_after);
                        stmts
                    },

                    &mir::Rvalue::NullaryOp(_op, ref _ty) => unimplemented!("{:?}", rhs),

                    &mir::Rvalue::Discriminant(ref src) => {
                        let discr_var = self.cfg_method.add_fresh_local_var(vir::Type::TypedRef(type_name));
                        let int_field = self.encoder.encode_value_field(ty);
                        let discr_field = self.encoder.encode_discriminant_field();
                        let (encoded_src, _, _) = self.encode_place(src);
                        // Obtain acc(encoded_src.discr_field)
                        stmts.push(
                            vir::Stmt::obtain_acc(encoded_src.clone().access(discr_field.clone()))
                        );
                        // Obtain acc(encoded_lhs)
                        stmts.push(
                            vir::Stmt::obtain_acc(encoded_src.clone().access(discr_field.clone()))
                        );
                        // Allocate the discr_var
                        stmts.extend(
                            self.encode_allocation(discr_var.clone().into(), ty)
                        );
                        // Initialize discr_var.int_field
                        stmts.push(
                            vir::Stmt::Assign(
                                vir::Place::Base(discr_var.clone()).access(int_field),
                                encoded_src.access(discr_field).into()
                            )
                        );
                        // Fold discr_var
                        stmts.push(
                            vir::Stmt::fold_pred(discr_var.clone().into())
                        );
                        // Assign encoded_lhs to encoded_lhs
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.clone(),
                                discr_var.into()
                            )
                        );
                        stmts
                    }

                    &mir::Rvalue::Aggregate(ref aggregate, ref operands) => {
                        let (encoded_value, before_stmts) = self.encode_assign_aggregate(ty, aggregate, operands);
                        stmts.extend(before_stmts);
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs,
                                encoded_value
                            )
                        );
                        stmts
                    }

                    &mir::Rvalue::Ref(ref _region, _borrow_kind, ref place) => {
                        let ref_var = self.cfg_method.add_fresh_local_var(vir::Type::TypedRef(type_name));
                        // Obtain acc(encoded_lhs)
                        stmts.push(
                            vir::Stmt::obtain_acc(encoded_lhs.clone())
                        );
                        // Allocate the ref_var
                        stmts.extend(
                            self.encode_allocation(ref_var.clone().into(), ty)
                        );
                        // Initialize ref_var.ref_field
                        let ref_field = self.encoder.encode_value_field(ty);
                        let (encoded_value, _, _) = self.encode_place(place);
                        stmts.push(
                            vir::Stmt::Assign(
                                vir::Place::Base(ref_var.clone()).access(ref_field),
                                encoded_value.into(),
                            )
                        );
                        // Fold ref_var
                        stmts.push(
                            vir::Stmt::fold_pred(ref_var.clone().into())
                        );
                        // Assign ref_var to encoded_lhs
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs,
                                ref_var.into()
                            )
                        );
                        stmts
                    }

                    ref x => unimplemented!("{:?}", x)
                }
            },

            ref x => unimplemented!("{:?}", x)
        }
    }

    fn encode_terminator(&mut self, term: &mir::Terminator<'tcx>,
                         cfg_blocks: &HashMap<BasicBlockIndex, CfgBlockIndex>,
                         spec_cfg_block: CfgBlockIndex,
                         abort_cfg_block: CfgBlockIndex,
                         return_cfg_block: CfgBlockIndex) -> (Vec<vir::Stmt>, Successor) {
        trace!("Encode terminator '{:?}'", term.kind);
        let mut stmts: Vec<vir::Stmt> = vec![];

        match term.kind {
            TerminatorKind::Return => {
                (stmts, Successor::Goto(return_cfg_block))
            },

            TerminatorKind::Goto { target } => {
                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::SwitchInt { ref targets, ref discr, ref values, switch_ty } => {
                trace!("SwitchInt ty '{:?}', discr '{:?}', values '{:?}'", switch_ty, discr, values);
                let mut cfg_targets: Vec<(vir::Expr, CfgBlockIndex)> = vec![];
                let discr_var = if switch_ty.sty == ty::TypeVariants::TyBool {
                    self.cfg_method.add_fresh_local_var(vir::Type::Bool)
                } else {
                    self.cfg_method.add_fresh_local_var(vir::Type::Int)
                };
                let (discr_tmp_val, effects_before_stmts, effect_after_stmts) = self.eval_operand(discr);
                stmts.extend(
                    effects_before_stmts
                );
                stmts.push(
                    vir::Stmt::Assign(
                        discr_var.clone().into(),
                        discr_tmp_val
                    )
                );
                stmts.extend(
                    effect_after_stmts
                );
                for (i, &value) in values.iter().enumerate() {
                    let target = targets[i as usize];
                    // Convert int to bool, if required
                    let viper_guard = if switch_ty.sty == ty::TypeVariants::TyBool {
                        if value == 0 {
                            // If discr is 0 (false)
                            vir::Expr::not(discr_var.clone().into())
                        } else {
                            // If discr is not 0 (true)
                            discr_var.clone().into()
                        }
                    } else {
                        vir::Expr::eq_cmp(
                            discr_var.clone().into(),
                            value.into()
                        )
                    };
                    let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                    cfg_targets.push((viper_guard, *target_cfg_block))
                }
                let default_target = targets[values.len()];
                let cfg_default_target = cfg_blocks.get(&default_target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::GotoSwitch(cfg_targets, *cfg_default_target))
            },

            TerminatorKind::Unreachable => {
                (stmts, Successor::Unreachable)
            },

            TerminatorKind::Abort => {
                (stmts, Successor::Goto(abort_cfg_block))
            },

            TerminatorKind::Drop { ref target, .. } => {
                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::FalseEdges { ref real_target, .. } => {
                let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::FalseUnwind { real_target, .. } => {
                let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::DropAndReplace { ref target, ref location, ref value, .. } => {
                let (encoded_loc, _, _) = self.encode_place(location);
                let (_, encoded_value, effects_before, effects_after) = self.encode_operand(value);
                stmts.extend(effects_before);
                if self.is_place_encoded_as_local_var(location) {
                    stmts.push(
                        vir::Stmt::Assign(encoded_loc, encoded_value.into())
                    );
                } else {
                    stmts.push(
                        vir::Stmt::Assign(encoded_loc, encoded_value.into())
                    );
                }
                stmts.extend(effects_after);
                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::Call {
                ref args,
                ref destination,
                func: mir::Operand::Constant(
                    box mir::Constant {
                        literal: mir::Literal::Value {
                            value: &ty::Const {
                                val: ConstVal::Unevaluated(def_id, _),
                                ..
                            }
                        },
                        ..
                    }
                ),
                ..
            } |
            TerminatorKind::Call {
                ref args,
                ref destination,
                func: mir::Operand::Constant(
                    box mir::Constant {
                        literal: mir::Literal::Value {
                            value: ty::Const {
                                ty: &ty::TyS {
                                    sty: ty::TyFnDef(def_id, ..),
                                    ..
                                },
                                ..
                            }
                        },
                        ..
                    }
                ),
                ..
            } => {
                let func_proc_name: &str = &self.encoder.env().get_item_name(def_id);
                match func_proc_name {
                    "prusti_contracts::internal::__assertion" => {
                        // This is a Prusti loop invariant
                        unreachable!();
                    },
                    "std::rt::begin_panic" => {
                        // This is called when a Rust assertion fails
                        stmts.push(vir::Stmt::comment(format!("Rust panic - {:?}", args[0])));
                        stmts.push(vir::Stmt::Assert(false.into(), vir::Id()));
                    },
                    _ => {
                    let mut stmts_after: Vec<vir::Stmt> = vec![];
                    let mut arg_vars = Vec::new();

                    for operand in args.iter() {
                        let (arg_var, _, effects_before, effects_after) = self.encode_operand(operand);
                        arg_vars.push(arg_var);
                        stmts.extend(effects_before);
                        stmts_after.extend(effects_after);
                    }

                    let mut encoded_targets = Vec::new();
                    let target = {
                        let &(ref target_place, _) = destination.as_ref().unwrap();
                        let (src, ty, _) = self.encode_place(target_place);
                        let local = self.locals.get_fresh(ty);
                        let viper_local = self.encode_prusti_local(local);
                        stmts_after.push(vir::Stmt::Assign(src, viper_local.clone().into()));
                        encoded_targets.push(viper_local);
                        local
                    };

                    let procedure_contract = self.encoder
                        .get_procedure_contract_for_call(def_id, &arg_vars, target);

                    let label = self.cfg_method.get_fresh_label_name();
                    stmts.push(vir::Stmt::Label(label.clone()));

                    let precondition = self.encode_precondition_expr(&procedure_contract);
                    stmts.push(vir::Stmt::Exhale(precondition, vir::Id()));

                    stmts.push(vir::Stmt::MethodCall(
                        self.encoder.encode_procedure_name(def_id),
                        vec![],
                        encoded_targets
                    ));

                    let (obtain_stmts, postcondition) = self.encode_postcondition_expr(&procedure_contract, &label);
                    stmts.extend(obtain_stmts);
                    stmts.push(vir::Stmt::Inhale(postcondition));

                    stmts.extend(stmts_after);
                    }
                }

                if let &Some((_, target)) = destination {
                    let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                    (stmts, Successor::Goto(*target_cfg_block))
                } else {
                    (stmts, Successor::Unreachable)
                }
            },

            TerminatorKind::Call { ..} => {
                // Other kind of calls?
                unimplemented!();
            },

            TerminatorKind::Assert { ref cond, expected, ref target, .. } => {
                trace!("Assert cond '{:?}', expected '{:?}'", cond, expected);
                let cond_var = self.cfg_method.add_fresh_local_var(vir::Type::Bool);
                let (cond_tmp_val, pre_effect_stmts, post_effect_stmts) = self.eval_operand(cond);
                stmts.extend(
                    pre_effect_stmts
                );
                stmts.push(
                    vir::Stmt::Assign(
                        cond_var.clone().into(),
                        cond_tmp_val
                    )
                );
                stmts.extend(
                    post_effect_stmts
                );
                let viper_guard = if expected {
                    cond_var.into()
                } else {
                    vir::Expr::not(cond_var.into())
                };
                let target_cfg_block = *cfg_blocks.get(&target).unwrap();
                (stmts, Successor::GotoSwitch(vec![(viper_guard, target_cfg_block)], abort_cfg_block))
            }

            TerminatorKind::Resume |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
        }
    }

    pub fn encode(mut self) -> vir::CfgMethod {
        debug!("Encode procedure {}", self.cfg_method.name());

        let mut procedure_contract = self.encoder.get_procedure_contract_for_def(self.proc_def_id);

        // Formal return
        for local in self.mir.local_decls.indices().take(1) {
            let name = self.encode_local_var_name(local);
            let type_name = self.encoder.encode_type_predicate_use(self.get_rust_local_ty(local));
            self.cfg_method.add_formal_return(&name, vir::Type::TypedRef(type_name))
        }

        let mut cfg_blocks: HashMap<BasicBlockIndex, CfgBlockIndex> = HashMap::new();

        // Initialize CFG blocks
        let start_cfg_block = self.cfg_method.add_block("start", vec![], vec![
            vir::Stmt::comment(format!("========== start =========="))
        ]);

        let mut first_cfg_block = true;
        self.procedure.walk_once_cfg(|bbi, _| {
            let cfg_block = self.cfg_method.add_block(&format!("{:?}", bbi), vec![], vec![
                vir::Stmt::comment(format!("========== {:?} ==========", bbi))
            ]);
            if first_cfg_block {
                self.cfg_method.set_successor(start_cfg_block, Successor::Goto(cfg_block));
                first_cfg_block = false;
            }
            cfg_blocks.insert(bbi, cfg_block);
        });

        let spec_cfg_block = self.cfg_method.add_block("spec", vec![], vec![
            vir::Stmt::comment(format!("========== spec ==========")),
            vir::Stmt::comment("This should never be reached. It's a residual of type-checking specifications."),
        ]);
        self.cfg_method.set_successor(spec_cfg_block, Successor::Unreachable);

        let abort_cfg_block = self.cfg_method.add_block("abort", vec![], vec![
            vir::Stmt::comment(format!("========== abort ==========")),
            vir::Stmt::comment("Target of any Rust panic."),
        ]);
        self.cfg_method.set_successor(abort_cfg_block, Successor::Unreachable);

        let return_cfg_block = self.cfg_method.add_block("return", vec![], vec![
            vir::Stmt::comment(format!("========== return ==========")),
            vir::Stmt::comment("Target of any 'return' statement."),
        ]);
        self.cfg_method.set_successor(return_cfg_block, Successor::Return);

        // Encode preconditions
        self.encode_preconditions(start_cfg_block, &mut procedure_contract);

        // Encode postcondition
        self.encode_postconditions(return_cfg_block, &mut procedure_contract);

        // Encode statements
        self.procedure.walk_once_cfg(|bbi, bb_data| {
            let statements: &Vec<mir::Statement<'tcx>> = &bb_data.statements;

            //TODO: Implement:
            //if self.loop_encoder.is_loop_head(bbi) {
                //self.encode_loop_invariant_inhale(bbi);
            //}

            // Encode statements
            for (stmt_index, stmt) in statements.iter().enumerate() {
                trace!("Encode statement {:?}:{}", bbi, stmt_index);
                let cfg_block = *cfg_blocks.get(&bbi).unwrap();
                self.cfg_method.add_stmt(cfg_block, vir::Stmt::comment(format!("[mir] {:?}", stmt)));
                let stmts = self.encode_statement(stmt);
                for stmt in stmts.into_iter() {
                    self.cfg_method.add_stmt(cfg_block, stmt);
                }
            }

            let successor_count = bb_data.terminator().successors().count();
            for successor in bb_data.terminator().successors() {
                if self.loops.is_loop_head(successor) {
                    assert!(successor_count == 1);
                    self.encode_loop_invariant_exhale(*successor, bbi);
                }
            }
        });

        // Encode terminators and set CFG edges
        self.procedure.walk_once_cfg(|bbi, bb_data| {
            if let Some(ref term) = bb_data.terminator {
                trace!("Encode terminator of {:?}", bbi);
                let cfg_block = *cfg_blocks.get(&bbi).unwrap();
                self.cfg_method.add_stmt(cfg_block, vir::Stmt::comment(format!("[mir] {:?}", term.kind)));
                let (stmts, successor) = self.encode_terminator(
                    term,
                    &cfg_blocks,
                    spec_cfg_block,
                    abort_cfg_block,
                    return_cfg_block
                );
                for stmt in stmts.into_iter() {
                    self.cfg_method.add_stmt(cfg_block, stmt);
                }
                self.cfg_method.set_successor(cfg_block, successor);
            }
        });

        let local_vars: Vec<_> = self.locals
            .iter()
            .filter(|local| !self.locals.is_return(*local))
            .collect();
        for local in local_vars.iter() {
            let type_name = self.encoder.encode_type_predicate_use(self.locals.get_type(*local));
            let var_name = self.locals.get_name(*local);
            self.cfg_method.add_local_var(&var_name, vir::Type::TypedRef(type_name));
        }

        let method_name = self.cfg_method.name();

        Log::report("vir_initial_method", &method_name, self.cfg_method.to_string());

        // Dump initial CFG
        Log::report_with_writer("graphviz_initial_method", &method_name, |writer| self.cfg_method.to_graphviz(writer));

        // Add fold/unfold
        let final_method = foldunfold::add_fold_unfold(self.cfg_method, self.encoder.get_used_viper_predicates_map());

        // Dump final CFG
        Log::report_with_writer("graphviz_method", &method_name, |writer| final_method.to_graphviz(writer));

        final_method
    }

    fn encode_place_predicate_permission(&self, place: vir::Place) -> vir::Expr {
        let predicate_name = place.typed_ref_name().unwrap();
        vir::Expr::PredicateAccessPredicate(
            box vir::Expr::PredicateAccess(
                predicate_name,
                vec![place.into()],
            ),
            vir::Perm::full(),
        )
    }

    /// Encode permissions that are implicitly carried by the given local variable.
    fn encode_local_variable_permission(&self, local: Local) -> vir::Expr {
        self.encode_place_predicate_permission(
            self.encode_prusti_local(local).into()
        )
    }

    /// Encode the precondition as a single expression.
    fn encode_precondition_expr(&self, contract: &ProcedureContract<'tcx>) -> vir::Expr {
        contract.args
            .iter()
            .map(|&local| self.encode_local_variable_permission(local))
            .conjoin()
    }

    /// Encode precondition inhale on the definition side.
    fn encode_preconditions(&mut self, start_cfg_block: CfgBlockIndex,
                            contract: &ProcedureContract<'tcx>) {
        self.cfg_method.add_stmt(start_cfg_block, vir::Stmt::comment("Preconditions:"));
        let expr = self.encode_precondition_expr(contract);
        let inhale_stmt = vir::Stmt::Inhale(expr);
        self.cfg_method.add_stmt(start_cfg_block, inhale_stmt);
        self.cfg_method.add_label_stmt(start_cfg_block, PRECONDITION_LABEL);
    }

    /// Encode permissions that are implicitly carried by the given place.
    /// `state_label` – the label of the state in which the place should
    /// be evaluated (the place expression is wrapped in the labelled old).
    fn encode_place_permission(&self, place: &Place<'tcx>, state_label: Option<&str>) -> vir::Expr {
        let (encoded_place, place_ty, _) = self.encode_generic_place(place);
        let predicate_name = self.encoder.encode_type_predicate_use(place_ty);
        vir::Expr::PredicateAccessPredicate(
            box vir::Expr::PredicateAccess(
                predicate_name,
                vec![
                    if let Some(label) = state_label {
                        vir::Expr::LabelledOld(box encoded_place.into(), label.to_string())
                    } else {
                        encoded_place.into()
                    }
                ]
            ),
            vir::Perm::full(),
        )
    }

    /// Encode the postcondition as a single expression with a sequence of "obtain" statements.
    fn encode_postcondition_expr(&self, contract: &ProcedureContract<'tcx>,
                                 label: &str) -> (Vec<vir::Stmt>, vir::Expr) {
        let mut obtain_stmts = Vec::new();
        let mut conjuncts = Vec::new();
        for place in contract.returned_refs.iter() {
            conjuncts.push(self.encode_place_permission(place, Some(label)));
        }
        for borrow_info in contract.borrow_infos.iter() {
            debug!("{:?}", borrow_info);
            let lhs = borrow_info.blocking_paths
                .iter()
                .map(|place| {
                    debug!("{:?}", place);
                    self.encode_place_permission(place, None)
                })
                .conjoin();
            let rhs = borrow_info.blocked_paths
                .iter()
                .map(|place| self.encode_place_permission(place, Some(label)))
                .conjoin();
            conjuncts.push(vir::Expr::MagicWand(box lhs, box rhs));
        }
        obtain_stmts.push(vir::Stmt::obtain_pred(self.encode_prusti_local(contract.returned_value).into()));
        conjuncts.push(self.encode_local_variable_permission(contract.returned_value));
        (obtain_stmts, conjuncts.into_iter().conjoin())
    }

    /// Encode postcondition exhale on the definition side.
    fn encode_postconditions(&mut self, return_cfg_block: CfgBlockIndex,
                             contract: &ProcedureContract<'tcx>) {
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::comment("Postconditions:"));
        let (obtain_stmts, postcondition) = self.encode_postcondition_expr(contract, PRECONDITION_LABEL);
        for obtain_stmt in obtain_stmts {
            self.cfg_method.add_stmt(return_cfg_block, obtain_stmt);
        }
        let exhale_stmt = vir::Stmt::Exhale(postcondition, vir::Id());
        self.cfg_method.add_stmt(return_cfg_block, exhale_stmt);
    }

    fn encode_loop_invariant_exhale(&mut self, _loop_head: BasicBlockIndex,
                                    _source: BasicBlockIndex) {
        // TODO: commented out because we need access to dataflow analysis (it requires a patch to rustc)
        //let _invariant = self.loops.compute_loop_invariant(loop_head, &mut self.dataflow_info);
    }

    fn get_rust_local_decl(&self, local: mir::Local) -> &mir::LocalDecl<'tcx> {
        &self.mir.local_decls[local]
    }

    fn get_rust_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.get_rust_local_decl(local).ty
    }

    fn encode_local_var_name(&self, local: mir::Local) -> String {
        /*let local_decl = self.get_rust_local_decl(local);
        match local_decl.name {
            Some(ref name) => format!("{:?}", name),
            None => format!("{:?}", local)
        }*/
        format!("{:?}", local)
    }

    fn encode_local(&self, local: mir::Local) -> vir::LocalVar {
        let var_name = self.encode_local_var_name(local);
        let type_name = self.encoder.encode_type_predicate_use(self.get_rust_local_ty(local));
        vir::LocalVar::new(var_name, vir::Type::TypedRef(type_name))
    }

    fn encode_prusti_local(&self, local: Local) -> vir::LocalVar {
        let var_name = self.locals.get_name(local);
        let type_name = self.encoder.encode_type_predicate_use(self.locals.get_type(local));
        vir::LocalVar::new(var_name, vir::Type::TypedRef(type_name))
    }

    /// Returns
    /// - `vir::Expr`: the expression of the projection;
    /// - `ty::Ty<'tcx>`: the type of the expression;
    /// - `Option<usize>`: optionally, the variant of the enum.
    fn encode_projection(&self, place_projection: &mir::PlaceProjection<'tcx>,
                         root: Option<Local>) -> (vir::Place, ty::Ty<'tcx>, Option<usize>) {
        debug!("Encode projection {:?} {:?}", place_projection, root);
        let (encoded_base, base_ty, opt_variant_index) = self.encode_place_with_subst_root(
            &place_projection.base, root);
        match &place_projection.elem {
            &mir::ProjectionElem::Field(ref field, _) => {
                match base_ty.sty {
                    ty::TypeVariants::TyBool |
                    ty::TypeVariants::TyInt(_) |
                    ty::TypeVariants::TyUint(_) |
                    ty::TypeVariants::TyRawPtr(_) |
                    ty::TypeVariants::TyRef(_, _, _) => panic!("Type {:?} has no fields", base_ty),

                    ty::TypeVariants::TyTuple(elems) => {
                        let field_name = format!("tuple_{}", field.index());
                        let field_ty = elems[field.index()];
                        let encoded_field = self.encoder.encode_ref_field(&field_name, field_ty);
                        let encoded_projection = encoded_base.access(encoded_field);
                        (encoded_projection, field_ty, None)
                    },

                    ty::TypeVariants::TyAdt(ref adt_def, ref subst) => {
                        debug!("subst {:?}", subst);
                        let num_variants = adt_def.variants.len();
                        // FIXME: why this can be None?
                        let variant_index = opt_variant_index.unwrap_or_else(|| {
                            assert!(num_variants == 1);
                            0
                        });
                        let tcx = self.encoder.env().tcx();
                        assert!(variant_index as u128 == adt_def.discriminant_for_variant(tcx, variant_index).val);
                        let field = &adt_def.variants[variant_index].fields[field.index()];
                        let field_name = if num_variants == 1 {
                            format!("struct_{}", field.name)
                        } else {
                            format!("enum_{}_{}", variant_index, field.name)
                        };
                        let field_ty = tcx.type_of(field.did);
                        let encoded_field = self.encoder.encode_ref_field(&field_name, field_ty);
                        let encoded_projection = encoded_base.access(encoded_field);
                        (encoded_projection, field_ty, None)
                    },

                    ref x => unimplemented!("{:?}", x),
                }
            },

            &mir::ProjectionElem::Deref => {
                match base_ty.sty {
                    ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty, .. }) |
                    ty::TypeVariants::TyRef(_, ty, _) => {
                        let ref_field = self.encoder.encode_ref_field("val_ref", ty);
                        let access = vir::Place::Field(
                            box encoded_base,
                            ref_field
                        );
                        (access, ty, None)
                    },
                    _ => unreachable!(),
                }
            },

            &mir::ProjectionElem::Downcast(ref adt_def, variant_index) => {
                debug!("Downcast projection {:?}, {:?}", adt_def, variant_index);
                (encoded_base, base_ty, Some(variant_index))
            },

            x => unimplemented!("{:?}", x),
        }
    }

    fn encode_place(&self, place: &mir::Place<'tcx>) -> (vir::Place, ty::Ty<'tcx>, Option<usize>) {
        self.encode_place_with_subst_root(place, None)
    }

    fn encode_generic_place(&self, place: &Place<'tcx>) -> (vir::Place, ty::Ty<'tcx>, Option<usize>) {
        match place {
            &Place::NormalPlace(ref place) => {
                self.encode_place_with_subst_root(place, None)
            },
            &Place::SubstitutedPlace { substituted_root, ref place } => {
                self.encode_place_with_subst_root(place, Some(substituted_root))
            },
        }
    }

    /// TODO: Need to take into account how much the place is already unfolded.
    /// Returns
    /// - `vir::Expr`: the expression of the projection;
    /// - `ty::Ty<'tcx>`: the type of the expression;
    /// - `Option<usize>`: optionally, the variant of the enum.
    fn encode_place_with_subst_root(&self, place: &mir::Place<'tcx>,
                                    root: Option<Local>) -> (vir::Place, ty::Ty<'tcx>, Option<usize>) {
        match place {
            &mir::Place::Local(local) =>
                match root {
                    Some(root) => (
                        self.encode_prusti_local(root).into(),
                        self.locals.get_type(root),
                        None
                    ),
                    None => (
                        self.encode_local(local).into(),
                        self.get_rust_local_ty(local),
                        None
                    ),
                },
            &mir::Place::Projection(ref place_projection) =>
                self.encode_projection(place_projection, root),
            x => unimplemented!("{:?}", x),
        }
    }

    fn eval_place(&mut self, place: &mir::Place<'tcx>) -> vir::Place {
        let (encoded_place, place_ty, _) = self.encode_place(place);
        let value_field = self.encoder.encode_value_field(place_ty);
        encoded_place.access(value_field)
    }

    fn is_place_encoded_as_local_var(&self, place: &mir::Place<'tcx>) -> bool {
        match place {
            &mir::Place::Local(_) => true,
            &mir::Place::Projection(_) => false,
            x => unimplemented!("{:?}", x),
        }
    }

    /// Returns:
    /// - an `vir::Expr` that corresponds to the value of the operand;
    /// - a vector `Vec<vir::Stmt>` of pre side effects.
    /// - a vector `Vec<vir::Stmt>` of post side effects.
    fn eval_operand(&mut self, operand: &mir::Operand<'tcx>) -> (vir::Expr, Vec<vir::Stmt>, Vec<vir::Stmt>) {
        match operand {
            &mir::Operand::Constant(box mir::Constant{ ty, literal: mir::Literal::Value{ value: &ty::Const{ ref val, .. } }, ..}) => {
                let is_bool_ty = ty.sty == ty::TypeVariants::TyBool;
                (self.encoder.eval_const_val(val, is_bool_ty), vec![], vec![])
            }
            &mir::Operand::Copy(ref place) => {
                let val_place = self.eval_place(place);
                // Before, obtain the place that is read
                let obtain_stmt = vir::Stmt::obtain_acc(val_place.clone());
                (val_place.into(), vec![obtain_stmt], vec![])
            },
            &mir::Operand::Move(ref place) =>{
                let (encoded_place, _, _) = self.encode_place(place);
                let val_place = self.eval_place(&place);
                // Before, obtain the place that is read
                let obtain_stmt = vir::Stmt::obtain_acc(val_place.clone());
                // After, uninitialize place
                let null_stmt  = vir::Stmt::Assign(
                    encoded_place,
                    vir::Const::Null.into()
                );
                (val_place.into(), vec![obtain_stmt], vec![null_stmt])
            },
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_operand(&mut self, operand: &mir::Operand<'tcx>) -> (Local,
                                                                   vir::LocalVar,
                                                                   Vec<vir::Stmt>,
                                                                   Vec<vir::Stmt>) {
        debug!("Encode operand {:?}", operand);
        match operand {
            &mir::Operand::Move(ref place) => {
                let (src, ty, _) = self.encode_place(place);
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                // Before, obtain the folded src
                let obtain_stmt = vir::Stmt::Obtain(self.encode_place_predicate_permission(src.clone()));
                // Before, move to a temporary variable (used to encode procedure calls)
                let stmt_before = vir::Stmt::Assign(viper_local.clone().into(), src.clone().into());
                // After, uninitialize src
                let stmt_after = vir::Stmt::Assign(src.clone(), vir::Const::Null.into());
                (local, viper_local, vec![obtain_stmt, stmt_before], vec![stmt_after])
            },
            &mir::Operand::Copy(ref place) => {
                let (src, ty, _) = self.encode_place(place);
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                let mut stmts: Vec<vir::Stmt> = vec![] ;
                // Before, obtain the folded src
                stmts.push(
                    vir::Stmt::Obtain(self.encode_place_predicate_permission(src.clone()))
                );
                // Before, copy the values from src to viper_local
                stmts.extend(
                    self.encode_copy(src, viper_local.clone().into(), ty)
                );
                (local, viper_local, stmts, vec![])
            },
            &mir::Operand::Constant(box mir::Constant{ ty, literal: mir::Literal::Value{ value: &ty::Const{ ref val, .. } }, ..}) => {
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                let mut stmts = Vec::new();
                // Before, allocate viper_local
                stmts.extend(self.encode_allocation(viper_local.clone().into(), ty));
                let is_bool_ty = ty.sty == ty::TypeVariants::TyBool;
                let const_val = self.encoder.eval_const_val(val, is_bool_ty);
                let field = self.encoder.encode_value_field(ty);
                // Before, initialize viper_local
                stmts.push(
                    vir::Stmt::Assign(vir::Place::from(viper_local.clone()).access(field), const_val)
                );
                // Before, fold viper_local
                stmts.push(
                    vir::Stmt::fold_pred(viper_local.clone().into())
                );
                (local, viper_local, stmts, vec![])
            },
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_havoc(&mut self, dst: vir::Place) -> Vec<vir::Stmt> {
        debug!("Encode havoc {:?}", dst);
        if let vir::Place::Base(dst_local_var) = dst.clone() {
            vec![
                vir::Stmt::New(dst_local_var, vec![]),
            ]
        } else {
            let type_name = dst.typed_ref_name().unwrap();
            let tmp_var = self.cfg_method.add_fresh_local_var(vir::Type::TypedRef(type_name));
            vec![
                vir::Stmt::New(tmp_var.clone(), vec![]),
                vir::Stmt::Assign(dst.into(), tmp_var.into()),
            ]
        }
    }

    fn encode_allocation(&mut self, dst: vir::Place, ty: ty::Ty<'tcx>) -> Vec<vir::Stmt> {
        debug!("Encode allocation {:?}", ty);
        let fields = self.encoder.encode_type_fields(ty);

        if let vir::Place::Base(dst_local_var) = dst.clone() {
            vec![
                vir::Stmt::New(
                    dst_local_var,
                    fields
                ),
            ]
        } else {
            let type_name = self.encoder.encode_type_predicate_use(ty);
            let tmp_var = self.cfg_method.add_fresh_local_var(vir::Type::TypedRef(type_name));
            vec![
                vir::Stmt::New(
                    tmp_var.clone(),
                    fields
                ),
                vir::Stmt::Assign(
                    dst.into(),
                    tmp_var.into()
                )
            ]
        }
    }

    fn encode_copy_expr(&mut self, src: vir::Place, dst: vir::Place, self_ty: ty::Ty<'tcx>) -> vir::Expr {
        debug!("Encode copy expr {:?}, {:?}, {:?}", src, dst, self_ty);

        let copy_exprs = match self_ty.sty {
            ty::TypeVariants::TyBool |
            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) => {
                let field = self.encoder.encode_value_field(self_ty);
                vec![
                    // Equality
                    vir::Expr::eq_cmp(
                        dst.clone().access(field.clone()).into(),
                        src.clone().access(field.clone()).into()
                    )
                ]
            },

            ty::TypeVariants::TyRawPtr(_) |
            ty::TypeVariants::TyRef(_, _, _) => {
                // It is not sound to copy a struct containing a mutable reference (full ownership)
                // Regarding mutable references, we dont' support them yet
                unimplemented!();
            },

            ty::TypeVariants::TyTuple(elems) => {
                let mut exprs: Vec<vir::Expr> = vec![];
                for (field_num, ty) in elems.iter().enumerate() {
                    let field_name = format!("tuple_{}", field_num);
                    let field = self.encoder.encode_ref_field(&field_name, ty);
                    exprs.push(
                        // Equality
                        self.encode_copy_expr(
                            src.clone().access(field.clone()),
                            dst.clone().access(field.clone()),
                            ty
                        )
                    );
                }
                exprs
            },

            ty::TypeVariants::TyAdt(ref adt_def, ref subst) => {
                let mut exprs: Vec<vir::Expr> = vec![];
                let discriminant_field = self.encoder.encode_discriminant_field();
                exprs.push(
                    // Copy discriminant
                    vir::Expr::eq_cmp(
                        src.clone().access(discriminant_field.clone()).into(),
                        dst.clone().access(discriminant_field.clone()).into()
                    )
                );
                let tcx = self.encoder.env().tcx();
                let num_variants = adt_def.variants.len();
                for (variant_index, variant_def) in adt_def.variants.iter().enumerate() {
                    let mut variant_exprs: Vec<vir::Expr> = vec![];
                    for field in &variant_def.fields {
                        let field_name = if num_variants == 1 {
                            format!("struct_{}", field.name)
                        } else {
                            format!("enum_{}_{}", variant_index, field.name)
                        };
                        let field_ty = field.ty(tcx, subst);
                        let elem_field = self.encoder.encode_ref_field(&field_name, field_ty);
                        variant_exprs.push(
                            // Equality
                            self.encode_copy_expr(
                                src.clone().access(elem_field.clone()),
                                dst.clone().access(elem_field.clone()),
                                field_ty
                            )
                        )
                    }
                    exprs.push(
                        vir::Expr::implies(
                            vir::Expr::eq_cmp(
                                src.clone().access(discriminant_field.clone()).into(),
                                variant_index.into()
                            ),
                            variant_exprs.into_iter().conjoin()
                        )
                    );
                }
                exprs
            },

            ref x => unimplemented!("{:?}", x),
        };

        vir::Expr::unfolding(
            src,
            vir::Expr::unfolding(
                dst,
                copy_exprs.into_iter().conjoin()
            )
        )
    }

    fn encode_copy(&mut self, src: vir::Place, dst: vir::Place, ty: ty::Ty<'tcx>) -> Vec<vir::Stmt> {
        debug!("Encode copy {:?}, {:?}, {:?}", src, dst, ty);

        let type_name = self.encoder.encode_type_predicate_use(ty);
        let tmp_var = self.cfg_method.add_fresh_local_var(vir::Type::TypedRef(type_name));
        let inhale_expr = self.encode_copy_expr(src, tmp_var.clone().into(), ty);

        vec![
            // Inhale permissions on `tmp_var`
            vir::Stmt::Inhale(self.encode_place_predicate_permission(tmp_var.clone().into())),
            // Assume equality with `src`
            vir::Stmt::Inhale(inhale_expr),
            // Assign and havoc `dst`
            vir::Stmt::Assign(
                dst.into(),
                tmp_var.into()
            )
        ]
    }

    fn encode_bin_op_value(&mut self, op: mir::BinOp, left: vir::Expr, right: vir::Expr) -> vir::Expr {
        match op {
            mir::BinOp::Gt => vir::Expr::gt_cmp(left, right),

            mir::BinOp::Add => vir::Expr::add(left, right),

            mir::BinOp::Sub => vir::Expr::sub(left, right),

            mir::BinOp::Eq => vir::Expr::eq_cmp(left, right),

            mir::BinOp::Ne => vir::Expr::not(vir::Expr::eq_cmp(left, right)),

            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_unary_op_value(&mut self, op: mir::UnOp, expr: vir::Expr) -> vir::Expr {
        match op {
            mir::UnOp::Not => vir::Expr::not(expr),

            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_bin_op_check(&mut self, op: mir::BinOp, _left: vir::Expr, _right: vir::Expr) -> vir::Expr {
        warn!("TODO: Encode bin op check {:?} ", op);
        // TODO
        true.into()
    }

    fn encode_assign_aggregate(
        &mut self,
        ty: ty::Ty<'tcx>,
        aggregate: &mir::AggregateKind<'tcx>,
        operands: &Vec<mir::Operand<'tcx>>
    ) -> (vir::Expr, Vec<vir::Stmt>) {
        debug!("Encode aggregate {:?}, {:?}", aggregate, operands);
        let type_name = self.encoder.encode_type_predicate_use(ty);
        let dst_var = self.cfg_method.add_fresh_local_var(vir::Type::TypedRef(type_name));
        let mut stmts: Vec<vir::Stmt> = vec![];
        stmts.extend(
            self.encode_allocation(dst_var.clone().into(), ty)
        );

        match aggregate {
            &mir::AggregateKind::Tuple => {
                let field_types = if let ty::TypeVariants::TyTuple(ref x) = ty.sty { x } else { unreachable!() };
                for (field_num, operand) in operands.iter().enumerate() {
                    let field_name = format!("tuple_{}", field_num);
                    let encoded_field = self.encoder.encode_ref_field(&field_name, field_types[field_num]);
                    let (_, encoded_operand, before_stmts, after_stmts) = self.encode_operand(operand);
                    stmts.extend(before_stmts);
                    stmts.push(
                        vir::Stmt::Assign(
                            vir::Place::from(dst_var.clone()).access(encoded_field),
                            encoded_operand.into()
                        )
                    );
                    stmts.extend(after_stmts);
                }
                (dst_var.clone().into(), stmts)
            },

            &mir::AggregateKind::Adt(adt_def, variant_index, _, _) => {
                let num_variants = adt_def.variants.len();
                if num_variants > 1 {
                    let discr_field = self.encoder.encode_discriminant_field();
                    stmts.push(
                        vir::Stmt::Assign(
                            vir::Place::from(dst_var.clone()).access(discr_field),
                            variant_index.into()
                        )
                    );
                };
                let variant_def = &adt_def.variants[variant_index];
                for (field_index, field) in variant_def.fields.iter().enumerate() {
                    let operand = &operands[field_index];
                    let field_name = if num_variants == 1 {
                        format!("struct_{}", field.name)
                    } else {
                        format!("enum_{}_{}", variant_index, field.name)
                    };
                    let tcx = self.encoder.env().tcx();
                    let field_ty = tcx.type_of(field.did);
                    let encoded_field = self.encoder.encode_ref_field(&field_name, field_ty);
                    let (_, encoded_operand, before_stmts, after_stmts) = self.encode_operand(operand);
                    stmts.extend(before_stmts);
                    stmts.push(
                        vir::Stmt::Assign(
                            vir::Place::from(dst_var.clone()).access(encoded_field),
                            encoded_operand.into()
                        )
                    );
                    stmts.extend(after_stmts);
                }
                (dst_var.into(), stmts)
            },

            ref x => unimplemented!("{:?}", x)
        }
    }
}
