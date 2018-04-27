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
use prusti_interface::environment::DataflowInfo;
use encoder::vil::{self, Successor, CfgBlockIndex};
use encoder::vil::utils::ExprIterator;

static PRECONDITION_LABEL: &'static str = "pre";

pub struct ProcedureEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: ProcedureDefId,
    procedure: &'p ProcedureImpl<'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    cfg_method: vil::CfgMethod,
    locals: LocalVariableManager<'tcx>,
    loops: LoopEncoder<'tcx>,
    dataflow_info: DataflowInfo<'tcx>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> ProcedureEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, procedure: &'p ProcedureImpl<'a, 'tcx>) -> Self {
        let cfg_method = vil::CfgMethod::new(
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
        let dataflow_info = procedure.construct_dataflow_info();

        ProcedureEncoder {
            encoder,
            proc_def_id: procedure.get_id(),
            procedure,
            mir: mir,
            cfg_method,
            locals: locals,
            loops: loops,
            dataflow_info: dataflow_info,
        }
    }

    fn encode_statement(&mut self, stmt: &mir::Statement<'tcx>) -> Vec<vil::Stmt> {
        debug!("Encode statement '{:?}'", stmt);
        let mut stmts: Vec<vil::Stmt> = vec![];

        match stmt.kind {
            mir::StatementKind::StorageDead(_) |
            mir::StatementKind::StorageLive(_) |
            mir::StatementKind::EndRegion(_) => stmts,

            mir::StatementKind::Assign(ref lhs, ref rhs) => {
                let (encoded_lhs, ty, _) = self.encode_place(lhs);
                match rhs {
                    &mir::Rvalue::Use(ref operand) => {
                        let (_, encoded_value, effects_before, effects_after) = self.encode_operand(operand);
                        stmts.extend(effects_before);
                        stmts.push(
                            vil::Stmt::Assign(encoded_lhs, encoded_value)
                        );
                        stmts.extend(effects_after);
                        stmts
                    },

                    &mir::Rvalue::BinaryOp(op, ref left, ref right) => {
                        let (encoded_left, effects_after_left) = self.eval_operand(left);
                        let (encoded_right, effects_after_right) = self.eval_operand(right);
                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.encode_bin_op_value(op, encoded_left, encoded_right);
                        stmts.push(
                            vil::Stmt::Assign(
                                encoded_lhs.access(field),
                                encoded_value
                            )
                        );
                        stmts.extend(effects_after_left);
                        stmts.extend(effects_after_right);
                        stmts
                    },

                    &mir::Rvalue::CheckedBinaryOp(op, ref left, ref right) => {
                        let (encoded_left, effects_after_left) = self.eval_operand(left);
                        let (encoded_right, effects_after_right) = self.eval_operand(right);
                        let encoded_value = self.encode_bin_op_value(op, encoded_left.clone(), encoded_right.clone());
                        let encoded_check = self.encode_bin_op_check(op, encoded_left, encoded_right);
                        let elems = if let ty::TypeVariants::TyTuple(ref x) = ty.sty { x } else { unreachable!() };
                        let value_field = self.encoder.encode_ref_field("tuple_0");
                        let value_field_value = self.encoder.encode_value_field(elems[0]);
                        let check_field = self.encoder.encode_ref_field("tuple_1");
                        let check_field_value = self.encoder.encode_value_field(elems[1]);
                        stmts.push(
                            vil::Stmt::Assign(
                                encoded_lhs.clone()
                                    .access(value_field)
                                    .access(value_field_value),
                                encoded_value,
                            )
                        );
                        stmts.push(
                            vil::Stmt::Assign(
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

                    &mir::Rvalue::UnaryOp(_op, ref _operand) => unimplemented!("{:?}", rhs),

                    &mir::Rvalue::NullaryOp(_op, ref _ty) => unimplemented!("{:?}", rhs),

                    &mir::Rvalue::Discriminant(ref src) => {
                        let discr_var = self.cfg_method.add_fresh_local_var(vil::Type::Ref);
                        stmts.extend(
                            self.encode_allocation(discr_var.clone().into(), ty)
                        );
                        let int_field = self.encoder.encode_value_field(ty);
                        let discr_field = self.encoder.encode_discriminant_field();
                        let (encoded_src, _, _) = self.encode_place(src);
                        stmts.push(
                            vil::Stmt::Assign(
                                encoded_lhs.clone(),
                                discr_var.into()
                            )
                        );
                        stmts.push(
                            vil::Stmt::Assign(
                                encoded_lhs.access(int_field),
                                encoded_src.access(discr_field).into()
                            )
                        );
                        stmts
                    }

                    &mir::Rvalue::Aggregate(ref aggregate, ref operands) => {
                        let (encoded_value, before_stmts) = self.encode_assign_aggregate(ty, aggregate, operands);
                        stmts.extend(before_stmts);
                        stmts.push(
                            vil::Stmt::Assign(
                                encoded_lhs,
                                encoded_value
                            )
                        );
                        stmts
                    }

                    &mir::Rvalue::Ref(ref _region, _borrow_kind, ref place) => {
                        let ref_var = self.cfg_method.add_fresh_local_var(vil::Type::Ref);
                        stmts.extend(
                            self.encode_allocation(ref_var.clone().into(), ty)
                        );
                        let field = self.encoder.encode_value_field(ty);
                        let (encoded_value, _, _) = self.encode_place(place);
                        stmts.push(
                            vil::Stmt::Assign(
                                encoded_lhs.clone(),
                                ref_var.into()
                            )
                        );
                        stmts.push(
                            vil::Stmt::Assign(
                                encoded_lhs.access(field),
                                encoded_value.into(),
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
                         return_cfg_block: CfgBlockIndex) -> (Vec<vil::Stmt>, Successor) {
        trace!("Encode terminator '{:?}'", term.kind);
        let mut stmts: Vec<vil::Stmt> = vec![];

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
                let mut cfg_targets: Vec<(vil::Expr, CfgBlockIndex)> = vec![];
                let discr_var = if switch_ty.sty == ty::TypeVariants::TyBool {
                    self.cfg_method.add_fresh_local_var(vil::Type::Bool)
                } else {
                    self.cfg_method.add_fresh_local_var(vil::Type::Int)
                };
                let (discr_tmp_val, effect_stmts) = self.eval_operand(discr);
                stmts.push(
                    vil::Stmt::Assign(
                        discr_var.clone().into(),
                        discr_tmp_val
                    )
                );
                stmts.extend(
                    effect_stmts
                );
                for (i, &value) in values.iter().enumerate() {
                    let target = targets[i as usize];
                    // Convert int to bool, if required
                    let viper_guard = if switch_ty.sty == ty::TypeVariants::TyBool {
                        if value == 0 {
                            // If discr is 0 (false)
                            vil::Expr::not(discr_var.clone().into())
                        } else {
                            // If discr is not 0 (true)
                            discr_var.clone().into()
                        }
                    } else {
                        vil::Expr::eq_cmp(
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
                        vil::Stmt::Assign(encoded_loc, encoded_value)
                    );
                } else {
                    stmts.push(
                        vil::Stmt::Assign(encoded_loc, encoded_value)
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
                        stmts.push(vil::Stmt::comment(format!("Rust panic - {:?}", args[0])));
                        stmts.push(vil::Stmt::Assert(false.into(), vil::Id()));
                    },
                    _ => {
                    let mut stmts_after: Vec<vil::Stmt> = vec![];
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
                        stmts_after.push(vil::Stmt::Assign(src, viper_local.clone().into()));
                        encoded_targets.push(viper_local);
                        local
                    };

                    let mut procedure_contract = self.encoder
                        .get_procedure_contract_for_call(def_id, &arg_vars, target);

                    let label = self.cfg_method.get_fresh_label_name();
                    stmts.push(vil::Stmt::Label(label.clone()));

                    let precondition = self.encode_precondition_expr(&procedure_contract);
                    stmts.push(vil::Stmt::Exhale(precondition, vil::Id()));

                    stmts.push(vil::Stmt::MethodCall(
                        self.encoder.encode_procedure_name(def_id),
                        vec![],
                        encoded_targets
                    ));

                    let postcondition = self.encode_postcondition_expr(&procedure_contract, &label);
                    stmts.push(vil::Stmt::Inhale(postcondition));

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
                let cond_var = self.cfg_method.add_fresh_local_var(vil::Type::Bool);
                let (cond_tmp_val, effect_stmts) = self.eval_operand(cond);
                stmts.push(
                    vil::Stmt::Assign(
                        cond_var.clone().into(),
                        cond_tmp_val
                    )
                );
                stmts.extend(
                    effect_stmts
                );
                let viper_guard = if expected {
                    cond_var.into()
                } else {
                    vil::Expr::not(cond_var.into())
                };
                let target_cfg_block = *cfg_blocks.get(&target).unwrap();
                (stmts, Successor::GotoSwitch(vec![(viper_guard, target_cfg_block)], abort_cfg_block))
            }

            TerminatorKind::Resume |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
        }
    }

    pub fn encode(mut self) -> vil::CfgMethod {
        let mut procedure_contract = self.encoder.get_procedure_contract_for_def(self.proc_def_id);

        // Formal return
        for local in self.mir.local_decls.indices().take(1) {
            let name = self.encode_local_var_name(local);
            self.cfg_method.add_formal_return(&name, vil::Type::Ref)
        }

        let mut cfg_blocks: HashMap<BasicBlockIndex, CfgBlockIndex> = HashMap::new();

        // Initialize CFG blocks
        let start_cfg_block = self.cfg_method.add_block("start", vec![], vec![
            vil::Stmt::comment(format!("========== start =========="))
        ]);

        let mut first_cfg_block = true;
        self.procedure.walk_once_cfg(|bbi, _| {
            let cfg_block = self.cfg_method.add_block(&format!("{:?}", bbi), vec![], vec![
                vil::Stmt::comment(format!("========== {:?} ==========", bbi))
            ]);
            if first_cfg_block {
                self.cfg_method.set_successor(start_cfg_block, Successor::Goto(cfg_block));
                first_cfg_block = false;
            }
            cfg_blocks.insert(bbi, cfg_block);
        });

        let spec_cfg_block = self.cfg_method.add_block("spec", vec![], vec![
            vil::Stmt::comment(format!("========== spec ==========")),
            vil::Stmt::comment("This should never be reached. It's a residual of type-checking specifications."),
        ]);
        self.cfg_method.set_successor(spec_cfg_block, Successor::Unreachable);

        let abort_cfg_block = self.cfg_method.add_block("abort", vec![], vec![
            vil::Stmt::comment(format!("========== abort ==========")),
            vil::Stmt::comment("Target of any Rust panic."),
        ]);
        self.cfg_method.set_successor(abort_cfg_block, Successor::Unreachable);

        let return_cfg_block = self.cfg_method.add_block("return", vec![], vec![
            vil::Stmt::comment(format!("========== return ==========")),
            vil::Stmt::comment("Target of any 'return' statement."),
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
                self.cfg_method.add_stmt(cfg_block, vil::Stmt::comment(format!("{:?}", stmt)));
                let stmts = self.encode_statement(stmt);
                for stmt in stmts.into_iter() {
                    self.cfg_method.add_stmt(cfg_block, stmt);
                }
            }

            let successor_count = bb_data.terminator().successors().len();
            for successor in bb_data.terminator().successors().iter() {
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
                self.cfg_method.add_stmt(cfg_block, vil::Stmt::comment(format!("{:?}", term.kind)));
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

        let var_names: Vec<_> = self.locals
            .iter()
            .filter(|local| !self.locals.is_return(*local))
            .map(|local| self.locals.get_name(local))
            .collect();
        for name in var_names.iter() {
            self.cfg_method.add_local_var(&name, vil::Type::Ref);
        }

        self.cfg_method
    }

    /// Encode permissions that are implicitly carried by the given local variable.
    fn encode_local_variable_permission(&self, local: Local) -> vil::Expr {
        let ty = self.locals.get_type(local);
        let predicate_name = self.encoder.encode_type_predicate_use(ty);
        vil::Expr::PredicateAccessPredicate(
            box vil::Expr::PredicateAccess(
                predicate_name,
                vec![self.encode_prusti_local(local).into()],
            ),
            vil::Perm::full(),
        )
    }

    /// Encode the precondition as a single expression.
    fn encode_precondition_expr(&self, contract: &ProcedureContract<'tcx>) -> vil::Expr {
        contract.args
            .iter()
            .map(|&local| self.encode_local_variable_permission(local))
            .conjoin()
    }

    /// Encode precondition inhale on the definition side.
    fn encode_preconditions(&mut self, start_cfg_block: CfgBlockIndex,
                            contract: &ProcedureContract<'tcx>) {
        self.cfg_method.add_stmt(start_cfg_block, vil::Stmt::comment("Preconditions:"));
        let expr = self.encode_precondition_expr(contract);
        let inhale_stmt = vil::Stmt::Inhale(expr);
        self.cfg_method.add_stmt(start_cfg_block, inhale_stmt);
        self.cfg_method.add_label_stmt(start_cfg_block, PRECONDITION_LABEL);
    }

    /// Encode permissions that are implicitly carried by the given place.
    /// `state_label` – the label of the state in which the place should
    /// be evaluated (the place expression is wrapped in the labelled old).
    fn encode_place_permission(&self, place: &Place<'tcx>, state_label: Option<&str>) -> vil::Expr {
        let (encoded_place, place_ty, _) = self.encode_generic_place(place);
        let predicate_name = self.encoder.encode_type_predicate_use(place_ty);
        vil::Expr::PredicateAccessPredicate(
            box vil::Expr::PredicateAccess(
                predicate_name,
                vec![
                    if let Some(label) = state_label {
                        vil::Expr::LabelledOld(box encoded_place.into(), label.to_string())
                    } else {
                        encoded_place.into()
                    }
                ]
            ),
            vil::Perm::full(),
        )
    }

    /// Encode the postcondition as a single expression.
    fn encode_postcondition_expr(&self, contract: &ProcedureContract<'tcx>,
                                 label: &str) -> vil::Expr {
        let mut conjuncts = Vec::new();
        for place in contract.returned_refs.iter() {
            conjuncts.push(self.encode_place_permission(place, Some(label)));
        }
        for borrow_info in contract.borrow_infos.iter() {
            debug!("{:?}", borrow_info);
            let mut lhs = borrow_info.blocking_paths
                .iter()
                .map(|place| {
                    debug!("{:?}", place);
                    self.encode_place_permission(place, None)
                })
                .conjoin();
            let mut rhs = borrow_info.blocked_paths
                .iter()
                .map(|place| self.encode_place_permission(place, Some(label)))
                .conjoin();
            conjuncts.push(vil::Expr::MagicWand(box lhs, box rhs));
        }
        conjuncts.push(self.encode_local_variable_permission(contract.returned_value));
        conjuncts.into_iter().conjoin()
    }

    /// Encode postcondition exhale on the definition side.
    fn encode_postconditions(&mut self, return_cfg_block: CfgBlockIndex,
                             contract: &ProcedureContract<'tcx>) {
        self.cfg_method.add_stmt(return_cfg_block, vil::Stmt::comment("Postconditions:"));
        let postcondition = self.encode_postcondition_expr(contract, PRECONDITION_LABEL);
        let exhale_stmt = vil::Stmt::Exhale(postcondition, vil::Id());
        self.cfg_method.add_stmt(return_cfg_block, exhale_stmt);
    }

    fn encode_loop_invariant_exhale(&mut self, loop_head: BasicBlockIndex,
                                    _source: BasicBlockIndex) {
        let _invariant = self.loops.compute_loop_invariant(loop_head, &mut self.dataflow_info);
        unimplemented!();
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

    fn encode_local(&self, local: mir::Local) -> vil::LocalVar {
        let var_name = self.encode_local_var_name(local);
        let var_type = self.encoder.ast_factory().ref_type();
        vil::LocalVar::new(var_name, vil::Type::Ref)
    }

    fn encode_prusti_local(&self, local: Local) -> vil::LocalVar {
        let var_name = self.locals.get_name(local);
        let var_type = self.encoder.ast_factory().ref_type();
        vil::LocalVar::new(var_name, vil::Type::Ref)
    }

    /// Returns
    /// - `vil::Expr`: the expression of the projection;
    /// - `ty::Ty<'tcx>`: the type of the expression;
    /// - `Option<usize>`: optionally, the variant of the enum.
    fn encode_projection(&self, place_projection: &mir::PlaceProjection<'tcx>,
                         root: Option<Local>) -> (vil::Place, ty::Ty<'tcx>, Option<usize>) {
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
                    ty::TypeVariants::TyRef(_, _) => panic!("Type {:?} has no fields", base_ty),

                    ty::TypeVariants::TyTuple(elems) => {
                        let field_name = format!("tuple_{}", field.index());
                        let field_ty = elems[field.index()];
                        let encoded_field = self.encoder.encode_ref_field(&field_name);
                        let encoded_projection = encoded_base.access(encoded_field);
                        (encoded_projection, field_ty, None)
                    },

                    ty::TypeVariants::TyAdt(ref adt_def, ref subst) => {
                        debug!("subst {:?}", subst);
                        let variant_index = opt_variant_index.unwrap_or(0);
                        let tcx = self.encoder.env().tcx();
                        assert!(variant_index as u128 == adt_def.discriminant_for_variant(tcx, variant_index).val);
                        let field = &adt_def.variants[variant_index].fields[field.index()];
                        let num_variants = adt_def.variants.len();
                        let field_name = if num_variants == 1 {
                            format!("struct_{}", field.name)
                        } else {
                            format!("enum_{}_{}", variant_index, field.name)
                        };
                        let field_ty = tcx.type_of(field.did);
                        let encoded_field = self.encoder.encode_ref_field(&field_name);
                        let encoded_projection = encoded_base.access(encoded_field);
                        (encoded_projection, field_ty, None)
                    },

                    ref x => unimplemented!("{:?}", x),
                }
            },

            &mir::ProjectionElem::Deref => {
                match base_ty.sty {
                    ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty, .. }) |
                    ty::TypeVariants::TyRef(_, ty::TypeAndMut { ty, .. }) => {
                        let ref_field = self.encoder.encode_ref_field("val_ref");
                        let access = vil::Place::Field(
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

    fn encode_place(&self, place: &mir::Place<'tcx>) -> (vil::Place, ty::Ty<'tcx>, Option<usize>) {
        self.encode_place_with_subst_root(place, None)
    }

    fn encode_generic_place(&self, place: &Place<'tcx>) -> (vil::Place, ty::Ty<'tcx>, Option<usize>) {
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
    /// - `vil::Expr`: the expression of the projection;
    /// - `ty::Ty<'tcx>`: the type of the expression;
    /// - `Option<usize>`: optionally, the variant of the enum.
    fn encode_place_with_subst_root(&self, place: &mir::Place<'tcx>,
                                    root: Option<Local>) -> (vil::Place, ty::Ty<'tcx>, Option<usize>) {
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

    fn eval_place(&mut self, place: &mir::Place<'tcx>) -> vil::Place {
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
    /// - an `vil::Expr` that corresponds to the value of the operand;
    /// - a vector `Vec<vil::Stmt>` of post side effects.
    fn eval_operand(&mut self, operand: &mir::Operand<'tcx>) -> (vil::Expr, Vec<vil::Stmt>) {
        match operand {
            &mir::Operand::Constant(box mir::Constant{ ty, literal: mir::Literal::Value{ value: &ty::Const{ ref val, .. } }, ..}) => {
                let is_bool_ty = ty.sty == ty::TypeVariants::TyBool;
                (self.encoder.eval_const_val(val, is_bool_ty), vec![])
            }
            &mir::Operand::Copy(ref place) => {
                (self.eval_place(place).into(), vec![])
            },
            &mir::Operand::Move(ref place) =>{
                let encoded_place = self.encode_place(place).0;
                let null_stmt  = vil::Stmt::Assign(
                    encoded_place,
                    vil::Const::Null.into()
                );
                (self.eval_place(place).into(), vec![null_stmt])
            },
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_operand(&mut self, operand: &mir::Operand<'tcx>) -> (Local,
                                                                   vil::Expr,
                                                                   Vec<vil::Stmt>,
                                                                   Vec<vil::Stmt>) {
        debug!("Encode operand {:?}", operand);
        match operand {
            &mir::Operand::Move(ref place) => {
                let (src, ty, _) = self.encode_place(place);
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                let stmt_before = vil::Stmt::Assign(viper_local.clone().into(), src.clone().into());
                let stmt_after = vil::Stmt::Assign(src, vil::Const::Null.into());
                (local, viper_local.into(), vec![stmt_before], vec![stmt_after])
            },
            &mir::Operand::Copy(ref place) => {
                let (src, ty, _) = self.encode_place(place);
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                let stmts = self.encode_copy(src, viper_local.clone().into(), ty);
                (local, viper_local.into(), stmts, vec![])
            },
            &mir::Operand::Constant(box mir::Constant{ ty, literal: mir::Literal::Value{ value: &ty::Const{ ref val, .. } }, ..}) => {
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                let mut stmts = Vec::new();
                stmts.extend(self.encode_allocation(viper_local.clone().into(), ty));
                let is_bool_ty = ty.sty == ty::TypeVariants::TyBool;
                let const_val = self.encoder.eval_const_val(val, is_bool_ty);
                let field = self.encoder.encode_value_field(ty);
                stmts.push(
                    vil::Stmt::Assign(vil::Place::from(viper_local.clone()).access(field), const_val)
                );
                (local, viper_local.into(), stmts, vec![])
            },
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_allocation(&mut self, dst: vil::Place, ty: ty::Ty<'tcx>) -> Vec<vil::Stmt> {
        debug!("Encode allocation {:?}", ty);
        let fields = self.encoder.encode_type_fields(ty);

        if let vil::Place::Base(dst_local_var) = dst.clone() {
            vec![
                vil::Stmt::New(
                    dst_local_var,
                    fields
                ),
            ]
        } else {
            let tmp_var = self.cfg_method.add_fresh_local_var(vil::Type::Ref);
            vec![
                vil::Stmt::New(
                    tmp_var.clone(),
                    fields
                ),
                vil::Stmt::Assign(
                    dst.into(),
                    tmp_var.into()
                )
            ]
        }
    }

    fn encode_copy(&mut self, src: vil::Place, dst: vil::Place, self_ty: ty::Ty<'tcx>) -> Vec<vil::Stmt> {
        debug!("Encode copy {:?}", self_ty);
        let mut stmts: Vec<vil::Stmt> = vec![];

        stmts.extend(
            self.encode_allocation(dst.clone(), self_ty)
        );

        let mut fields = self.encoder.encode_type_fields(self_ty);

        match self_ty.sty {
            ty::TypeVariants::TyBool |
            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) => {
                for field in fields.drain(..) {
                    stmts.push(
                        vil::Stmt::Assign(
                            dst.clone().access(field.clone()),
                            src.clone().access(field.clone()).into()
                        )
                    );
                }
            }

            ty::TypeVariants::TyRawPtr(_) |
            ty::TypeVariants::TyRef(_, _) => {
                let ref_field = self.encoder.encode_ref_field("val_ref");
                stmts.push(
                    vil::Stmt::Assign(
                        dst.access(ref_field.clone()),
                        src.access(ref_field).into()
                    )
                );
            },

            _ => {
                for field in fields.drain(..) {
                    let inner_src = src.clone().access(field.clone());
                    let inner_dst = dst.clone().access(field.clone());
                    if let vil::Type::TypedRef(predicate_name) = field.typ {
                        let field_ty = self.encoder.get_predicate_type(predicate_name).unwrap();
                        stmts.extend(
                            self.encode_copy(inner_src, inner_dst, field_ty)
                        );
                    } else {
                        stmts.push(
                            vil::Stmt::Assign(
                                dst.clone().access(field.clone()),
                                src.clone().access(field.clone()).into()
                            )
                        );
                    }
                }
            }
        };

        stmts
    }

    fn encode_bin_op_value(&mut self, op: mir::BinOp, left: vil::Expr, right: vil::Expr) -> vil::Expr {
        match op {
            mir::BinOp::Gt => vil::Expr::gt_cmp(left, right),

            mir::BinOp::Add => vil::Expr::add(left, right),

            mir::BinOp::Sub => vil::Expr::sub(left, right),

            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_bin_op_check(&mut self, op: mir::BinOp, _left: vil::Expr, _right: vil::Expr) -> vil::Expr {
        warn!("TODO: Encode bin op check {:?} ", op);
        // TODO
        true.into()
    }

    fn encode_assign_aggregate(
        &mut self,
        ty: ty::Ty<'tcx>,
        aggregate: &mir::AggregateKind<'tcx>,
        operands: &Vec<mir::Operand<'tcx>>
    ) -> (vil::Expr, Vec<vil::Stmt>) {
        debug!("Encode aggregate {:?}, {:?}", aggregate, operands);
        let dst_var = self.cfg_method.add_fresh_local_var(vil::Type::Ref);
        let mut stmts: Vec<vil::Stmt> = vec![];
        stmts.extend(
            self.encode_allocation(dst_var.clone().into(), ty)
        );

        match aggregate {
            &mir::AggregateKind::Tuple => {
                for (field_num, operand) in operands.iter().enumerate() {
                    let field_name = format!("tuple_{}", field_num);
                    let encoded_field = self.encoder.encode_ref_field(&field_name);
                    let (_, encoded_operand, before_stmts, after_stmts) = self.encode_operand(operand);
                    stmts.extend(before_stmts);
                    stmts.push(
                        vil::Stmt::Assign(
                            vil::Place::from(dst_var.clone()).access(encoded_field),
                            encoded_operand
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
                        vil::Stmt::Assign(
                            vil::Place::from(dst_var.clone()).access(discr_field),
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
                    let encoded_field = self.encoder.encode_ref_field(&field_name);
                    let (_, encoded_operand, before_stmts, after_stmts) = self.encode_operand(operand);
                    stmts.extend(before_stmts);
                    stmts.push(
                        vil::Stmt::Assign(
                            vil::Place::from(dst_var.clone()).access(encoded_field),
                            encoded_operand
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
