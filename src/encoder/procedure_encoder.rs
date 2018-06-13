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
use std::collections::HashSet;
use prusti_interface::environment::BasicBlockIndex;
use rustc::mir::TerminatorKind;
use rustc::middle::const_val::ConstVal;
use encoder::Encoder;
use encoder::borrows::ProcedureContract;
use rustc_data_structures::indexed_vec::Idx;
use encoder::places::{Local, LocalVariableManager, Place};
use encoder::loop_encoder::LoopEncoder;
use encoder::builtin_encoder::BuiltinMethodKind;
use encoder::vir::{self, Successor, CfgBlockIndex};
use encoder::vir::utils::ExprIterator;
use encoder::foldunfold;
use report::Log;
use encoder::error_manager::ErrorCtxt;
use encoder::error_manager::PanicCause;


static PRECONDITION_LABEL: &'static str = "pre";

pub struct ProcedureEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: ProcedureDefId,
    procedure: &'p ProcedureImpl<'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    cfg_method: vir::CfgMethod,
    locals: LocalVariableManager<'tcx>,
    loops: LoopEncoder<'tcx>,
    auxiliar_local_vars: HashMap<String, vir::Type>,
    //dataflow_info: DataflowInfo<'tcx>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> ProcedureEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, procedure: &'p ProcedureImpl<'a, 'tcx>) -> Self {
        debug!("ProcedureEncoder constructor");

        let cfg_method = vir::CfgMethod::new(
            // method name
            encoder.encode_procedure_name(procedure.get_id()),
            // formal args
            vec![],
            // formal returns
            vec![],
            // local vars
            vec![],
            // reserved labels
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
            auxiliar_local_vars: HashMap::new()
            //dataflow_info: dataflow_info,
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
            vir::Stmt::Assert(
                false.into(),
                self.encoder.error_manager().register(ErrorCtxt::Unexpected())
            )
        ]);
        self.cfg_method.set_successor(spec_cfg_block, Successor::Return);

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
                self.cfg_method.add_stmt    (cfg_block, vir::Stmt::comment(format!("[mir] {:?}", term.kind)));
                let (stmts, successor) = self.encode_terminator(
                    term,
                    &cfg_blocks,
                    spec_cfg_block,
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

    fn encode_statement(&mut self, stmt: &mir::Statement<'tcx>) -> Vec<vir::Stmt> {
        debug!("Encode statement '{:?}', span: {:?}", stmt.kind, stmt.source_info.span);
        let mut stmts: Vec<vir::Stmt> = vec![];

        match stmt.kind {
            mir::StatementKind::StorageDead(_) |
            mir::StatementKind::StorageLive(_) |
            mir::StatementKind::EndRegion(_) => stmts,

            mir::StatementKind::Assign(ref lhs, ref rhs) => {
                let (encoded_lhs, ty, _) = self.encode_place(lhs);
                let type_name = self.encoder.encode_type_predicate_use(ty);
                match rhs {
                    &mir::Rvalue::Use(ref operand) => {
                        stmts.extend(
                            self.encode_assign_operand(&encoded_lhs, operand)
                        );
                        stmts
                    },

                    &mir::Rvalue::Aggregate(ref aggregate, ref operands) => {
                        stmts.extend(
                            self.encode_assign_aggregate(&encoded_lhs, ty, aggregate, operands)
                        );
                        stmts
                    }

                    &mir::Rvalue::BinaryOp(op, ref left, ref right) => {
                        let encoded_left = self.eval_operand(left);
                        let encoded_right = self.eval_operand(right);
                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.encode_bin_op_value(op, encoded_left, encoded_right, ty);
                        // Reset `lhs`
                        stmts.extend(
                            self.encode_havoc_and_allocation(&encoded_lhs.clone().into(), ty)
                        );
                        // Initialize lhs.field
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.access(field),
                                encoded_value
                            )
                        );
                        stmts
                    },

                    &mir::Rvalue::CheckedBinaryOp(op, ref left, ref right) => {
                        let encoded_left = self.eval_operand(left);
                        let encoded_right = self.eval_operand(right);
                        let encoded_value = self.encode_bin_op_value(op, encoded_left.clone(), encoded_right.clone(), ty);
                        let encoded_check = self.encode_bin_op_check(op, encoded_left, encoded_right);
                        let field_types = if let ty::TypeVariants::TyTuple(ref x) = ty.sty { x } else { unreachable!() };
                        let value_field = self.encoder.encode_ref_field("tuple_0", field_types[0]);
                        let value_field_value = self.encoder.encode_value_field(field_types[0]);
                        let check_field = self.encoder.encode_ref_field("tuple_1", field_types[1]);
                        let check_field_value = self.encoder.encode_value_field(field_types[1]);
                        // Reset `lhs`
                        stmts.extend(
                            self.encode_havoc_and_allocation(&encoded_lhs.clone().into(), ty)
                        );
                        // Initialize lhs.field
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
                        stmts
                    },

                    &mir::Rvalue::UnaryOp(op, ref operand)  => {
                        let encoded_val = self.eval_operand(operand);
                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.encode_unary_op_value(op, encoded_val);
                        // Reset `lhs`
                        stmts.extend(
                            self.encode_havoc_and_allocation(&encoded_lhs.clone().into(), ty)
                        );
                        // Initialize `lhs.field`
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.access(field),
                                encoded_value
                            )
                        );
                        stmts
                    },

                    &mir::Rvalue::NullaryOp(_op, ref _ty) => unimplemented!("{:?}", rhs),

                    &mir::Rvalue::Discriminant(ref src) => {
                        let (encoded_src, src_ty, _) = self.encode_place(src);
                        match src_ty.sty {
                            ty::TypeVariants::TyAdt(ref adt_def, _) => {
                                let num_variants = adt_def.variants.len();
                                // Reset `lhs`
                                stmts.extend(
                                    self.encode_havoc_and_allocation(&encoded_lhs.clone().into(), ty)
                                );
                                // Initialize `lhs.int_field`
                                let discr_field = self.encoder.encode_discriminant_field();
                                let discr_value: vir::Expr = if num_variants <= 1 {
                                    0.into()
                                } else {
                                    encoded_src.access(discr_field).into()
                                };
                                let int_field = self.encoder.encode_value_field(ty);
                                stmts.push(
                                    vir::Stmt::Assign(
                                        encoded_lhs.clone().access(int_field),
                                        discr_value
                                    )
                                );
                                stmts
                            }
                            ref x => {
                                debug!("The discriminant of type {:?} is not defined", x);
                                stmts
                            }
                        }

                    }

                    &mir::Rvalue::Ref(ref _region, _borrow_kind, ref place) => {
                        // Reset `lhs`
                        stmts.extend(
                            self.encode_havoc_and_allocation(&encoded_lhs.clone().into(), ty)
                        );
                        let ref_field = self.encoder.encode_value_field(ty);
                        let (encoded_value, _, _) = self.encode_place(place);
                        // Initialize ref_var.ref_field
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.clone().access(ref_field),
                                encoded_value.into(),
                            )
                        );
                        stmts
                    }

                    ref rhs => {
                        // Reset `lhs`
                        stmts.extend(
                            self.encode_havoc_and_allocation(&encoded_lhs.clone().into(), ty)
                        );
                        warn!("TODO: incomplete endcoding of '{:?}'", rhs);
                        stmts
                    }
                }
            },

            ref x => unimplemented!("{:?}", x)
        }
    }

    fn encode_terminator(&mut self, term: &mir::Terminator<'tcx>,
                         cfg_blocks: &HashMap<BasicBlockIndex, CfgBlockIndex>,
                         spec_cfg_block: CfgBlockIndex,
                         return_cfg_block: CfgBlockIndex) -> (Vec<vir::Stmt>, Successor) {
        trace!("Encode terminator '{:?}', span: {:?}", term.kind, term.source_info.span);
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
                let discr_val = self.eval_operand(discr);
                for (i, &value) in values.iter().enumerate() {
                    let target = targets[i as usize];
                    // Convert int to bool, if required
                    let viper_guard = if switch_ty.sty == ty::TypeVariants::TyBool {
                        if value == 0 {
                            // If discr is 0 (false)
                            vir::Expr::not(discr_val.clone().into())
                        } else {
                            // If discr is not 0 (true)
                            discr_val.clone().into()
                        }
                    } else {
                        vir::Expr::eq_cmp(
                            discr_val.clone().into(),
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
                let pos_id = self.encoder.error_manager().register(ErrorCtxt::UnreachableTerminator(term.source_info.span));
                stmts.push(
                    vir::Stmt::Assert(false.into(), pos_id)
                );
                (stmts, Successor::Return)
            },

            TerminatorKind::Abort => {
                let pos_id = self.encoder.error_manager().register(ErrorCtxt::AbortTerminator(term.source_info.span));
                stmts.push(
                    vir::Stmt::Assert(false.into(), pos_id)
                );
                (stmts, Successor::Return)
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
                stmts.extend(
                    self.encode_assign_operand(&encoded_loc, value)
                );
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
                        // args[0]: message
                        // args[1]: position of failing assertions
                        stmts.push(vir::Stmt::comment(format!("Rust panic - {:?}", args[0])));

                        // Pattern match on the macro that generated the panic
                        // TODO: use a better approach to match macros
                        let macro_backtrace = term.source_info.span.macro_backtrace();
                        debug!("macro_backtrace: {:?}", macro_backtrace);

                        let panic_cause = if !macro_backtrace.is_empty() {
                            let macro_name = term.source_info.span.macro_backtrace()[0].macro_decl_name.clone();
                            // HACK to match the filename of the span
                            let def_site_span = format!("{:?}", term.source_info.span.macro_backtrace()[0].def_site_span);

                            match macro_name.as_str() {
                                "panic!" if def_site_span.contains("<panic macros>") => {
                                    if macro_backtrace.len() > 1 {
                                        let second_macro_name = term.source_info.span.macro_backtrace()[1].macro_decl_name.clone();
                                        // HACK to match the filename of the span
                                        let second_def_site_span = format!("{:?}", term.source_info.span.macro_backtrace()[1].def_site_span);

                                        match second_macro_name.as_str() {
                                            "panic!" if second_def_site_span.contains("<panic macros>") => PanicCause::Panic,
                                            "assert!" if second_def_site_span == "None" => PanicCause::Assert,
                                            "unreachable!" if second_def_site_span.contains("<unreachable macros>") => PanicCause::Unreachable,
                                            _ => PanicCause::Panic
                                        }
                                    } else {
                                        PanicCause::Panic
                                    }
                                },
                                _ => PanicCause::Unknown
                            }
                        } else {
                            // Something else called panic!()
                            PanicCause::Unknown
                        };
                        let pos_id = self.encoder.error_manager().register(ErrorCtxt::Panic(term.source_info.span, panic_cause));
                        stmts.push(vir::Stmt::Assert(false.into(), pos_id));
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
                        let pos_id = self.encoder.error_manager().register(ErrorCtxt::ExhalePrecondition());
                        stmts.push(vir::Stmt::Exhale(precondition, pos_id));

                        stmts.push(vir::Stmt::MethodCall(
                            self.encoder.encode_procedure_name(def_id),
                            vec![],
                            encoded_targets
                        ));

                        let postcondition = self.encode_postcondition_expr(&procedure_contract, &label);
                        stmts.push(vir::Stmt::Inhale(postcondition));

                        stmts.extend(stmts_after);
                    }
                }

                if let &Some((_, target)) = destination {
                    let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                    (stmts, Successor::Goto(*target_cfg_block))
                } else {
                    // Unreachable
                    stmts.push(
                        vir::Stmt::Inhale(false.into())
                    );
                    (stmts, Successor::Return)
                }
            },

            TerminatorKind::Call { ..} => {
                // Other kind of calls?
                unimplemented!();
            },

            TerminatorKind::Assert { ref cond, expected, ref target, ref msg, .. } => {
                trace!("Assert cond '{:?}', expected '{:?}'", cond, expected);
                let cond_val = self.eval_operand(cond);
                let viper_guard = if expected {
                    cond_val
                } else {
                    vir::Expr::not(cond_val)
                };
                let target_cfg_block = *cfg_blocks.get(&target).unwrap();

                // Prepare a block that encodes the branch of the failure
                let failure_label = self.cfg_method.get_fresh_label_name();
                let failure_block = self.cfg_method.add_block(&failure_label, vec![], vec![
                    vir::Stmt::comment(format!("========== {} ==========", &failure_label)),
                    vir::Stmt::comment(format!("A Rust assertion failed: {}", msg.description())),
                    vir::Stmt::Assert(
                        false.into(),
                        self.encoder.error_manager().register(ErrorCtxt::AssertTerminator(term.source_info.span, msg.description().to_string()))
                    ),
                ]);
                self.cfg_method.set_successor(failure_block, Successor::Return);

                (stmts, Successor::GotoSwitch(vec![(viper_guard, target_cfg_block)], failure_block))
            }

            TerminatorKind::Resume |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
        }
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
        self.cfg_method.add_stmt(start_cfg_block, vir::Stmt::Label(PRECONDITION_LABEL.to_string()));
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

    /// Encode the postcondition as a single expression.
    fn encode_postcondition_expr(&self, contract: &ProcedureContract<'tcx>,
                                 label: &str) -> vir::Expr {
        let mut conjuncts = Vec::new();
        for place in contract.returned_refs.iter() {
            debug!("Put permission {:?} in postcondition", place);
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
        conjuncts.push(self.encode_local_variable_permission(contract.returned_value));
        conjuncts.into_iter().conjoin()
    }

    /// Encode postcondition exhale on the definition side.
    fn encode_postconditions(&mut self, return_cfg_block: CfgBlockIndex,
                             contract: &ProcedureContract<'tcx>) {
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::comment("Postconditions:"));
        let postcondition = self.encode_postcondition_expr(contract, PRECONDITION_LABEL);
        let pos_id = self.encoder.error_manager().register(ErrorCtxt::ExhalePostcondition());
        let exhale_stmt = vir::Stmt::Exhale(postcondition, pos_id);
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

    // TODO: What is this?
    fn encode_prusti_local(&self, local: Local) -> vir::LocalVar {
        let var_name = self.locals.get_name(local);
        let type_name = self.encoder.encode_type_predicate_use(self.locals.get_type(local));
        vir::LocalVar::new(var_name, vir::Type::TypedRef(type_name))
    }

    /// Returns
    /// - `vir::Place`: the place of the projection;
    /// - `ty::Ty<'tcx>`: the type of the place;
    /// - `Option<usize>`: optionally, the variant of the enum.
    fn encode_projection(&self, place_projection: &mir::PlaceProjection<'tcx>, root: Option<Local>)
                        -> (vir::Place, ty::Ty<'tcx>, Option<usize>) {
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
                        let field_name = format!("enum_{}_{}", variant_index, field.ident.as_str());
                        let field_ty = field.ty(tcx, subst);
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
                    ty::TypeVariants::TyAdt(ref adt_def, ref subst) if adt_def.is_box() => {
                        // Ugly hardcoded fields to dereference box
                        let tcx = self.encoder.env().tcx();
                        let field_1_ty = adt_def.variants[0].fields[0].ty(tcx, subst);
                        let ref_field_1 = self.encoder.encode_ref_field("enum_0_0", field_1_ty);
                        let field_2_ty = if let ty::TypeVariants::TyAdt(ref field_1_did, ref field_1_subst) = field_1_ty.sty {
                            field_1_did.variants[0].fields[0].ty(tcx, field_1_subst)
                        } else {
                            unreachable!()
                        };
                        let ref_field_2 = self.encoder.encode_ref_field("enum_0_pointer", field_2_ty);
                        let field_3_ty = if let ty::TypeVariants::TyAdt(ref field_2_did, ref field_2_subst) = field_2_ty.sty {
                            field_2_did.variants[0].fields[0].ty(tcx, field_2_subst)
                        } else {
                            unreachable!()
                        };
                        let ref_field_3 = self.encoder.encode_ref_field("enum_0_0", field_3_ty);
                        let field_4_ty = if let ty::TypeVariants::TyRawPtr(ty_and_mut) = field_3_ty.sty {
                            ty_and_mut.ty
                        } else {
                            unreachable!()
                        };
                        assert_eq!(field_4_ty, base_ty.boxed_ty());
                        let ref_field_4 = self.encoder.encode_ref_field("val_ref", field_4_ty);
                        let access = vir::Place::Field(
                            box vir::Place::Field(
                                box vir::Place::Field(
                                    box vir::Place::Field(
                                        box encoded_base,
                                        ref_field_1
                                    ),
                                    ref_field_2
                                ),
                                ref_field_3
                            ),
                            ref_field_4
                        );
                        (access, base_ty.boxed_ty(), None)
                    }
                    ref x => unimplemented!("{:?}", x),
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

    /// Returns an `vir::Expr` that corresponds to the value of the operand
    fn eval_operand(&mut self, operand: &mir::Operand<'tcx>) -> vir::Expr {
        match operand {
            &mir::Operand::Constant(box mir::Constant{ ty, literal: mir::Literal::Value{ value }, ..}) => {
                self.encoder.eval_const(value)
            }
            &mir::Operand::Copy(ref place) => {
                let val_place = self.eval_place(place);
                val_place.into()
            },
            &mir::Operand::Move(ref place) =>{
                let (encoded_place, _, _) = self.encode_place(place);
                let val_place = self.eval_place(&place);
                val_place.into()
            },
            x => unimplemented!("{:?}", x)
        }
    }

    fn get_operand_ty(&mut self, operand: &mir::Operand<'tcx>) -> ty::Ty<'tcx> {
        debug!("Get operand ty {:?}", operand);
        match operand {
            &mir::Operand::Move(ref place) => {
                let (_, ty, _) = self.encode_place(place);
                ty
            },
            &mir::Operand::Copy(ref place) => {
                let (_, ty, _) = self.encode_place(place);
                ty
            },
            &mir::Operand::Constant(box mir::Constant{ ty, ..}) => {
                ty
            },
        }
    }

    fn encode_operand_moved_place(&mut self, operand: &mir::Operand<'tcx>) -> Option<vir::Place> {
        debug!("Encode operand moved place {:?}", operand);
        match operand {
            &mir::Operand::Move(ref place) => {
                let (src, _, _) = self.encode_place(place);
                Some(src)
            },
            &mir::Operand::Copy(_) |
            &mir::Operand::Constant(_) => {
                None
            },
        }
    }

    /// Return type:
    /// - `Vec<vir::Stmt>`: the statements that encode the assignment of `operand` to `lhs`
    fn encode_assign_operand(&mut self, lhs: &vir::Place, operand: &mir::Operand<'tcx>) -> Vec<vir::Stmt> {
        debug!("Encode assign operand {:?}", operand);
        match operand {
            &mir::Operand::Move(ref place) => {
                let (src, _, _) = self.encode_place(place);
                // Move `src` to `lhs`
                vec![
                    vir::Stmt::Assign(lhs.clone().into(), src.clone().into())
                ]
            },
            &mir::Operand::Copy(ref place) => {
                let (src, ty, _) = self.encode_place(place);
                let mut stmts: Vec<vir::Stmt> = vec![] ;
                // Copy the values from `src` to `lhs`
                self.encode_copy(src, lhs.clone(), ty)
            },
            &mir::Operand::Constant(box mir::Constant{ ty, ref literal, ..}) => {
                let mut stmts = Vec::new();
                // Reset `lhs`
                stmts.extend(self.encode_havoc_and_allocation(lhs, ty));
                // Initialize the constant
                match literal {
                    mir::Literal::Value { value } => {
                        let const_val = self.encoder.eval_const(value);
                        let field = self.encoder.encode_value_field(ty);
                        // Initialize value of lhs
                        stmts.push(
                            vir::Stmt::Assign(lhs.clone().access(field), const_val)
                        );
                    }
                    mir::Literal::Promoted { index } => {
                        trace!("promoted constant literal {:?}: {:?}", index, ty);
                        trace!("{:?}", self.mir.promoted[*index].basic_blocks());
                        trace!("{:?}", self.mir.promoted[*index].basic_blocks().into_iter().next().unwrap().statements[0]);
                        // TODO
                        warn!("TODO: encoding of promoted constant literal '{:?}: {:?}' is incomplete", index, ty);
                        // Workaround: do not initialize values
                    }
                }
                stmts
            },
        }
    }

    /// Deprecated function. Use `encode_assign_operand` instead.
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
                // Before, move to a temporary variable (used to encode procedure calls)
                let stmt_before = vir::Stmt::Assign(viper_local.clone().into(), src.clone().into());
                (local, viper_local, vec![stmt_before], vec![])
            },
            &mir::Operand::Copy(ref place) => {
                let (src, ty, _) = self.encode_place(place);
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                let mut stmts: Vec<vir::Stmt> = vec![] ;
                // Before, copy the values from src to viper_local
                stmts.extend(
                    self.encode_copy(src, viper_local.clone().into(), ty)
                );
                (local, viper_local, stmts, vec![])
            },
            &mir::Operand::Constant(box mir::Constant{ ty, ref literal, ..}) => {
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                let mut stmts = Vec::new();
                // Before, allocate viper_local
                stmts.extend(self.encode_havoc_and_allocation(&viper_local.clone().into(), ty));
                let field = self.encoder.encode_value_field(ty);
                // Evaluate the constant
                /* TODO: in the future use the following commented code (not exposed by the compiler)
                let tcx = self.encoder.env().tcx();
                let const_prop = ConstPropagator::new(self.mir, tcx, MirSource::item(self.proc_def_id));
                let evaluated_const = const_prop.eval_constant(constant);
                let const_val = self.encoder.eval_const(value);
                */
                match literal {
                    mir::Literal::Value { value } => {
                        let const_val = self.encoder.eval_const(value);
                        // Before, initialize viper_local
                        stmts.push(
                            vir::Stmt::Assign(vir::Place::from(viper_local.clone()).access(field), const_val)
                        );
                    }
                    mir::Literal::Promoted { index } => {
                        trace!("promoted constant literal {:?}: {:?}", index, ty);
                        trace!("{:?}", self.mir.promoted[*index].basic_blocks());
                        trace!("{:?}", self.mir.promoted[*index].basic_blocks().into_iter().next().unwrap().statements[0]);
                        // TODO
                        warn!("TODO: encoding of promoted constant literal '{:?}: {:?}' is incomplete", index, ty);
                        /*
                        let tcx = self.encoder.env().tcx();
                        let const_prop = ConstPropagator::new(self.mir, tcx, MirSource::item(self.proc_def_id));
                        let evaluated_const = const_prop.eval_constant(constant);
                        let const_val = self.encoder.eval_const(value);
                        */
                        // Workaround: allocate viper_local.field
                        stmts.push(
                            vir::Stmt::Inhale(
                                self.encode_place_predicate_permission(
                                    vir::Place::from(viper_local.clone()).access(field)
                                )
                            )
                        );

                    }
                }
                (local, viper_local, stmts, vec![])
            },
        }
    }

    pub fn get_auxiliar_local_var(&mut self, suffix: &str, vir_type: vir::Type) -> vir::LocalVar {
        let name = format!("_aux_{}_{}", suffix, vir_type.name());
        if self.auxiliar_local_vars.contains_key(&name) {
            assert_eq!(self.auxiliar_local_vars[&name], vir_type);
        } else {
            self.cfg_method.add_local_var(&name, vir_type.clone());
            self.auxiliar_local_vars.insert(name.clone(), vir_type.clone());
        }
        vir::LocalVar::new(name, vir_type)
    }

    fn encode_havoc(&mut self, dst: &vir::Place, ty: ty::Ty<'tcx>) -> Vec<vir::Stmt> {
        debug!("Encode havoc {:?}", dst);
        let havoc_ref_method_name = self.encoder.encode_builtin_method_use(BuiltinMethodKind::HavocRef);
        if let &vir::Place::Base(ref dst_local_var) = dst {
            vec![
                vir::Stmt::MethodCall(havoc_ref_method_name, vec![], vec![dst_local_var.clone()]),
            ]
        } else {
            let tmp_var = self.get_auxiliar_local_var("havoc", self.encoder.encode_type(ty));
            vec![
                vir::Stmt::MethodCall(havoc_ref_method_name, vec![], vec![tmp_var.clone()]),
                vir::Stmt::Assign(dst.clone().into(), tmp_var.into()),
            ]
        }
    }

    /// Havoc and assume permission on fields
    fn encode_havoc_and_allocation(&mut self, dst: &vir::Place, ty: ty::Ty<'tcx>) -> Vec<vir::Stmt> {
        debug!("Encode havoc and allocation {:?}, {:?}", dst, ty);

        let mut stmts = vec![];
        // Havoc `dst`
        stmts.extend(
            self.encode_havoc(dst, ty)
        );
        // Allocate `dst`
        stmts.push(
            vir::Stmt::Inhale(
                self.encode_place_predicate_permission(dst.clone())
            )
        );
        stmts
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
                let num_variants = adt_def.variants.len();
                let discriminant_field = self.encoder.encode_discriminant_field();
                if num_variants > 1 {
                    exprs.push(
                        // Copy discriminant
                        vir::Expr::eq_cmp(
                            src.clone().access(discriminant_field.clone()).into(),
                            dst.clone().access(discriminant_field.clone()).into()
                        )
                    );
                }
                let tcx = self.encoder.env().tcx();
                for (variant_index, variant_def) in adt_def.variants.iter().enumerate() {
                    let mut variant_exprs: Vec<vir::Expr> = vec![];
                    for field in &variant_def.fields {
                        let field_name = format!("enum_{}_{}", variant_index, field.ident.as_str());
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
                    if num_variants > 1 {
                        exprs.push(
                            vir::Expr::implies(
                                vir::Expr::eq_cmp(
                                    src.clone().access(discriminant_field.clone()).into(),
                                    variant_index.into()
                                ),
                                variant_exprs.into_iter().conjoin()
                            )
                        );
                    } else {
                        exprs.push(
                            variant_exprs.into_iter().conjoin()
                        );
                    }
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

        let mut stmts = vec![];
        stmts.extend(
            // Reset `dst`
            self.encode_havoc_and_allocation(&dst.clone(), ty)
        );
        stmts.push(
            // Assume equality with `src`
            vir::Stmt::Inhale(
                self.encode_copy_expr(src, dst, ty)
            )
        );
        stmts
    }

    fn encode_bin_op_value(&mut self, op: mir::BinOp, left: vir::Expr, right: vir::Expr, ty: ty::Ty<'tcx>) -> vir::Expr {
        let is_bool = ty.sty == ty::TypeVariants::TyBool;
        match op {
            mir::BinOp::Eq => vir::Expr::eq_cmp(left, right),
            mir::BinOp::Ne => vir::Expr::not(vir::Expr::eq_cmp(left, right)),
            mir::BinOp::Gt => vir::Expr::gt_cmp(left, right),
            mir::BinOp::Ge => vir::Expr::ge_cmp(left, right),
            mir::BinOp::Lt => vir::Expr::lt_cmp(left, right),
            mir::BinOp::Le => vir::Expr::le_cmp(left, right),
            mir::BinOp::Add => vir::Expr::add(left, right),
            mir::BinOp::Sub => vir::Expr::sub(left, right),
            mir::BinOp::Rem => {
                let abs_right = vir::Expr::ite(
                    vir::Expr::ge_cmp(right.clone(), 0.into()),
                    right.clone(),
                    vir::Expr::minus(right.clone())
                );
                vir::Expr::ite(
                    vir::Expr::ge_cmp(left.clone(), 0.into()),
                    // positive value
                    vir::Expr::modulo(left.clone(), right.clone()),
                    // negative value
                    vir::Expr::sub(vir::Expr::modulo(left, right), abs_right),
                )
            }
            mir::BinOp::Div => vir::Expr::div(left, right),
            mir::BinOp::Mul => vir::Expr::mul(left, right),
            mir::BinOp::BitAnd if is_bool => vir::Expr::and(left, right),
            mir::BinOp::BitOr if is_bool => vir::Expr::or(left, right),
            mir::BinOp::BitXor if is_bool => vir::Expr::not(vir::Expr::eq_cmp(left, right)),
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_unary_op_value(&mut self, op: mir::UnOp, expr: vir::Expr) -> vir::Expr {
        match op {
            mir::UnOp::Not => vir::Expr::not(expr),
            mir::UnOp::Neg => vir::Expr::minus(expr),
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_bin_op_check(&mut self, op: mir::BinOp, _left: vir::Expr, _right: vir::Expr) -> vir::Expr {
        warn!("TODO: encoding of bin op check '{:?}' is incomplete", op);
        // TODO
        false.into()
    }

    fn encode_assign_aggregate(
        &mut self,
        dst: &vir::Place,
        ty: ty::Ty<'tcx>,
        aggregate: &mir::AggregateKind<'tcx>,
        operands: &Vec<mir::Operand<'tcx>>
    ) -> Vec<vir::Stmt> {
        debug!("Encode aggregate {:?}, {:?}", aggregate, operands);
        let mut stmts: Vec<vir::Stmt> = vec![];
        // Reset `dst`
        stmts.extend(
            self.encode_havoc_and_allocation(dst, ty)
        );
        // Initialize values
        match aggregate {
            &mir::AggregateKind::Tuple => {
                let field_types = if let ty::TypeVariants::TyTuple(ref x) = ty.sty { x } else { unreachable!() };
                for (field_num, operand) in operands.iter().enumerate() {
                    let field_name = format!("tuple_{}", field_num);
                    let encoded_field = self.encoder.encode_ref_field(&field_name, field_types[field_num]);
                    stmts.extend(
                        self.encode_assign_operand(&dst.clone().access(encoded_field), operand)
                    );
                }
                stmts
            },

            &mir::AggregateKind::Adt(adt_def, variant_index, subst, _) => {
                let num_variants = adt_def.variants.len();
                if num_variants > 1 {
                    let discr_field = self.encoder.encode_discriminant_field();
                    stmts.push(
                        vir::Stmt::Inhale(
                            vir::Expr::eq_cmp(
                                dst.clone().access(discr_field).into(),
                                variant_index.into()
                            )
                        )
                    );
                };
                let variant_def = &adt_def.variants[variant_index];
                for (field_index, field) in variant_def.fields.iter().enumerate() {
                    let operand = &operands[field_index];
                    let field_name = format!("enum_{}_{}", variant_index, field.ident.as_str());
                    let tcx = self.encoder.env().tcx();
                    let field_ty = field.ty(tcx, subst);
                    let encoded_field = self.encoder.encode_ref_field(&field_name, field_ty);
                    stmts.extend(
                        self.encode_assign_operand(&dst.clone().access(encoded_field), operand)
                    );
                }
                stmts
            },

            ref x => unimplemented!("{:?}", x)
        }
    }
}
