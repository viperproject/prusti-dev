// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::borrows::ProcedureContract;
use encoder::builtin_encoder::BuiltinMethodKind;
use encoder::Encoder;
use encoder::error_manager::ErrorCtxt;
use encoder::error_manager::PanicCause;
use encoder::foldunfold;
use encoder::loop_encoder::LoopEncoder;
use encoder::places::{Local, LocalVariableManager, Place};
use encoder::vir::{self, CfgBlockIndex, Successor};
use encoder::vir::ExprIterator;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::BasicBlockIndex;
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;
use prusti_interface::environment::ProcedureImpl;
use prusti_interface::report::Log;
use rustc::middle::const_val::ConstVal;
use rustc::mir;
use rustc::mir::TerminatorKind;
use rustc::ty;
use rustc_data_structures::indexed_vec::Idx;
use std::collections::HashMap;
use std::collections::HashSet;
use syntax::codemap::Span;
use prusti_interface::specifications::*;
use syntax::ast;
use encoder::mir_encoder::MirEncoder;
use encoder::mir_encoder::PRECONDITION_LABEL;

pub struct ProcedureEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: ProcedureDefId,
    procedure: &'p ProcedureImpl<'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    cfg_method: vir::CfgMethod,
    locals: LocalVariableManager<'tcx>,
    loops: LoopEncoder<'p, 'tcx>,
    auxiliar_local_vars: HashMap<String, vir::Type>,
    //dataflow_info: DataflowInfo<'tcx>,
    mir_encoder: MirEncoder<'p, 'v, 'r, 'a, 'tcx>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> ProcedureEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, procedure: &'p ProcedureImpl<'a, 'tcx>) -> Self {
        debug!("ProcedureEncoder constructor");

        let cfg_method = vir::CfgMethod::new(
            // method name
            encoder.encode_item_name(procedure.get_id()),
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
        let loops = LoopEncoder::new(mir, encoder.env().tcx(), procedure.get_id());
        // let dataflow_info = procedure.construct_dataflow_info();

        ProcedureEncoder {
            encoder,
            proc_def_id: procedure.get_id(),
            procedure,
            mir,
            cfg_method,
            locals,
            loops,
            auxiliar_local_vars: HashMap::new(),
            //dataflow_info: dataflow_info,
            mir_encoder: MirEncoder::new(encoder, mir, procedure.get_id())
        }
    }

    pub fn encode_name(&self) -> String {
        self.cfg_method.name()
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
                self.encoder.error_manager().register(
                    self.mir.span,
                    ErrorCtxt::Unexpected
                ),
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
            for &successor in bb_data.terminator().successors() {
                if self.loops.is_loop_head(successor) {
                    assert!(successor_count == 1);
                    self.encode_loop_invariant_exhale(successor, bbi);
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
                    return_cfg_block,
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

        // Allocate stack frame: formal return and local variables
        // (formal arguments are already inhaled by the precondition)
        self.cfg_method.add_stmt(start_cfg_block, vir::Stmt::comment("Allocate formal return and local variables"));
        let local_vars_and_return: Vec<_> = self.locals
            .iter()
            .filter(|local| !self.locals.is_formal_arg(self.mir, *local))
            .collect();
        for local in local_vars_and_return.iter() {
            let type_name = self.encoder.encode_type_predicate_use(self.locals.get_type(*local));
            let var_name = self.locals.get_name(*local);
            let var_type = vir::Type::TypedRef(type_name.clone());
            let local_var = vir::LocalVar::new(var_name.clone(), var_type);
            let alloc_stmt = vir::Stmt::Inhale(
                self.encode_place_predicate_permission(local_var.clone().into())
            );
            self.cfg_method.add_stmt(start_cfg_block, alloc_stmt);
        }

        /*
        // Keep a copy of the value of the variable (fixes issue #20)
        let formal_args: Vec<_> = self.locals
            .iter()
            .filter(|local| self.locals.is_formal_arg(self.mir, *local))
            .collect();
        for local in formal_args.iter() {
            let type_name = self.encoder.encode_type_predicate_use(self.locals.get_type(*local));
            let var_name = self.locals.get_name(*local);
            let old_var_name = format!("_old{}", var_name);
            let var_type = vir::Type::TypedRef(type_name.clone());
            let old_var_type = vir::Type::TypedRef(type_name.clone());
            let local_var = vir::LocalVar::new(var_name.clone(), var_type);
            let old_local_var = vir::LocalVar::new(old_var_name.clone(), old_var_type.clone());
            self.cfg_method.add_local_var(&old_var_name, old_var_type);
            let init_old = vir::Stmt::Inhale(
                vir::Expr::eq_cmp(
                    old_local_var.into(),
                    local_var.into()
                )
            );
            self.cfg_method.add_stmt(start_cfg_block, init_old);
        }

        // Fix evaluation of arguments in old states (see issue #20)
        for local in self.mir.local_decls.indices() {
            let local_var = self.encode_local(local);
            let old_var_name = format!("_old{}", local_var.name);
            let old_local_var = vir::LocalVar::new(old_var_name, local_var.typ.clone());
            trace!("replace {} --> {}", local_var, old_local_var);
            let local_var_ref: &vir::Place = &local_var.into();
            let old_local_var_ref: &vir::Place = &old_local_var.into();
            self.cfg_method.substitute_expr(
                |expr| expr.map_old_expr(
                    |label, old_expr| {
                        if label == PRECONDITION_LABEL {
                            old_expr.substitute_place_with_place(local_var_ref, old_local_var_ref.clone())
                        } else {
                            // See issue #20
                            warn!("TODO: local variables may be evaluated in the wrong state");
                            old_expr
                        }
                    }
                )
            );
        }
        */

        let method_name = self.cfg_method.name();

        self.encoder.log_vir_program_before_foldunfold(self.cfg_method.to_string());

        // Dump initial CFG
        Log::report_with_writer("graphviz_method_before_foldunfold", format!("{}.dot", method_name), |writer| self.cfg_method.to_graphviz(writer));

        // Add fold/unfold
        let final_method = foldunfold::add_fold_unfold(self.cfg_method, self.encoder.get_used_viper_predicates_map());

        // Dump final CFG
        Log::report_with_writer("graphviz_method_before_viper", format!("{}.dot", method_name), |writer| final_method.to_graphviz(writer));

        final_method
    }

    fn encode_statement(&mut self, stmt: &mir::Statement<'tcx>) -> Vec<vir::Stmt> {
        debug!("Encode statement '{:?}', span: {:?}", stmt.kind, stmt.source_info.span);
        let mut stmts: Vec<vir::Stmt> = vec![];

        match stmt.kind {
            mir::StatementKind::StorageDead(_) |
            mir::StatementKind::StorageLive(_) |
            mir::StatementKind::EndRegion(_) |
            mir::StatementKind::ReadForMatch(_) |
            mir::StatementKind::Nop => stmts,

            mir::StatementKind::Assign(ref lhs, ref rhs) => {
                let (encoded_lhs, ty, _) = self.encode_place(lhs);
                let type_name = self.encoder.encode_type_predicate_use(ty);
                match rhs {
                    &mir::Rvalue::Use(ref operand) => {
                        stmts.extend(
                            self.encode_assign_operand(&encoded_lhs, operand)
                        );
                        stmts
                    }

                    &mir::Rvalue::Aggregate(ref aggregate, ref operands) => {
                        stmts.extend(
                            self.encode_assign_aggregate(&encoded_lhs, ty, aggregate, operands)
                        );
                        stmts
                    }

                    &mir::Rvalue::BinaryOp(op, ref left, ref right) => {
                        let encoded_left = self.encode_operand_expr(left);
                        let encoded_right = self.encode_operand_expr(right);
                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.encode_bin_op_expr(op, encoded_left, encoded_right, ty);
                        // Initialize lhs.field
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.access(field),
                                encoded_value,
                                vir::AssignKind::Copy
                            )
                        );
                        stmts
                    }

                    &mir::Rvalue::CheckedBinaryOp(op, ref left, ref right) => {
                        let encoded_left = self.encode_operand_expr(left);
                        let encoded_right = self.encode_operand_expr(right);
                        let encoded_value = self.encode_bin_op_expr(op, encoded_left.clone(), encoded_right.clone(), ty);
                        let encoded_check = self.encode_bin_op_check(op, encoded_left, encoded_right);
                        let field_types = if let ty::TypeVariants::TyTuple(ref x) = ty.sty { x } else { unreachable!() };
                        let value_field = self.encoder.encode_ref_field("tuple_0", field_types[0]);
                        let value_field_value = self.encoder.encode_value_field(field_types[0]);
                        let check_field = self.encoder.encode_ref_field("tuple_1", field_types[1]);
                        let check_field_value = self.encoder.encode_value_field(field_types[1]);
                        // Initialize lhs.field
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.clone()
                                    .access(value_field)
                                    .access(value_field_value),
                                encoded_value,
                                vir::AssignKind::Copy
                            )
                        );
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs
                                    .access(check_field)
                                    .access(check_field_value),
                                encoded_check,
                                vir::AssignKind::Copy
                            )
                        );
                        stmts
                    }

                    &mir::Rvalue::UnaryOp(op, ref operand) => {
                        let encoded_val = self.encode_operand_expr(operand);
                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.encode_unary_op_expr(op, encoded_val);
                        // Initialize `lhs.field`
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.access(field),
                                encoded_value,
                                vir::AssignKind::Copy
                            )
                        );
                        stmts
                    }

                    &mir::Rvalue::NullaryOp(op, ref op_ty) => {
                        match op {
                            mir::NullOp::Box => {
                                assert_eq!(op_ty, &ty.boxed_ty());
                                let ref_field = self.encoder.encode_ref_field("val_ref", op_ty);

                                let box_content = vir::Place::Field(
                                    box encoded_lhs.clone(),
                                    ref_field,
                                );

                                // Allocate `box_content`
                                stmts.extend(
                                    self.encode_havoc_and_allocation(&box_content, op_ty)
                                );

                                // Leave `box_content` uninitialized
                            }
                            mir::NullOp::SizeOf => unimplemented!(),
                        };
                        stmts
                    }

                    &mir::Rvalue::Discriminant(ref src) => {
                        let (encoded_src, src_ty, _) = self.encode_place(src);
                        match src_ty.sty {
                            ty::TypeVariants::TyAdt(ref adt_def, _) if !adt_def.is_box() => {
                                let num_variants = adt_def.variants.len();
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
                                        discr_value,
                                        vir::AssignKind::Copy
                                    )
                                );
                                stmts
                            }

                            ty::TypeVariants::TyInt(_) |
                            ty::TypeVariants::TyUint(_) => {
                                let value_field = self.encoder.encode_value_field(src_ty);
                                let discr_value: vir::Expr = encoded_src.access(value_field).into();
                                let int_field = self.encoder.encode_value_field(ty);
                                stmts.push(
                                    vir::Stmt::Assign(
                                        encoded_lhs.clone().access(int_field),
                                        discr_value,
                                        vir::AssignKind::Copy
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

                    &mir::Rvalue::Ref(ref _region, mir::BorrowKind::Shared, ref place) => {
                        warn!("TODO: Incomplete encoding of shared references");
                        stmts
                    }

                    &mir::Rvalue::Ref(ref _region, mir::BorrowKind::Unique, ref place) |
                    &mir::Rvalue::Ref(ref _region, mir::BorrowKind::Mut{ .. }, ref place)=> {
                        let ref_field = self.encoder.encode_value_field(ty);
                        let (encoded_value, _, _) = self.encode_place(place);
                        // Havoc lhs (fixes issue #1)
                        stmts.extend(
                            self.encode_havoc_and_allocation(&encoded_lhs, ty)
                        );
                        // Initialize ref_var.ref_field
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.clone().access(ref_field),
                                encoded_value.into(),
                                vir::AssignKind::MutableBorrow
                            )
                        );
                        stmts
                    }

                    ref rhs => {
                        unimplemented!("encoding of '{:?}'", rhs);
                    }
                }
            }

            ref x => unimplemented!("{:?}", x)
        }
    }

    fn encode_terminator(&mut self, term: &mir::Terminator<'tcx>,
                         cfg_blocks: &HashMap<BasicBlockIndex, CfgBlockIndex>,
                         spec_cfg_block: CfgBlockIndex,
                         return_cfg_block: CfgBlockIndex) -> (Vec<vir::Stmt>, Successor) {
        debug!("Encode terminator '{:?}', span: {:?}", term.kind, term.source_info.span);
        let mut stmts: Vec<vir::Stmt> = vec![];

        match term.kind {
            TerminatorKind::Return => {
                (stmts, Successor::Goto(return_cfg_block))
            }

            TerminatorKind::Goto { target } => {
                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            }

            TerminatorKind::SwitchInt { ref targets, ref discr, ref values, switch_ty } => {
                trace!("SwitchInt ty '{:?}', discr '{:?}', values '{:?}'", switch_ty, discr, values);
                let mut cfg_targets: Vec<(vir::Expr, CfgBlockIndex)> = vec![];
                let discr_val = self.encode_operand_expr(discr);
                for (i, &value) in values.iter().enumerate() {
                    let target = targets[i as usize];
                    // Convert int to bool, if required
                    let viper_guard = match switch_ty.sty {
                        ty::TypeVariants::TyBool => {
                            if value == 0 {
                                // If discr is 0 (false)
                                vir::Expr::not(discr_val.clone().into())
                            } else {
                                // If discr is not 0 (true)
                                discr_val.clone().into()
                            }
                        }

                        ty::TypeVariants::TyInt(_) |
                        ty::TypeVariants::TyUint(_) => {
                            vir::Expr::eq_cmp(
                                discr_val.clone().into(),
                                self.encoder.encode_int_cast(value, switch_ty)
                            )
                        }

                        ref x => unreachable!("{:?}", x)
                    };
                    let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                    cfg_targets.push((viper_guard, *target_cfg_block))
                }
                let default_target = targets[values.len()];
                let cfg_default_target = cfg_blocks.get(&default_target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::GotoSwitch(cfg_targets, *cfg_default_target))
            }

            TerminatorKind::Unreachable => {
                let pos = self.encoder.error_manager().register(
                    term.source_info.span,
                    ErrorCtxt::UnreachableTerminator
                );
                stmts.push(
                    vir::Stmt::Assert(false.into(), pos)
                );
                (stmts, Successor::Return)
            }

            TerminatorKind::Abort => {
                let pos = self.encoder.error_manager().register(
                    term.source_info.span,
                    ErrorCtxt::AbortTerminator
                );
                stmts.push(
                    vir::Stmt::Assert(false.into(), pos)
                );
                (stmts, Successor::Return)
            }

            TerminatorKind::Drop { ref target, .. } => {
                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            }

            TerminatorKind::FalseEdges { ref real_target, .. } => {
                let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            }

            TerminatorKind::FalseUnwind { real_target, .. } => {
                let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            }

            TerminatorKind::DropAndReplace { ref target, ref location, ref value, .. } => {
                let (encoded_loc, _, _) = self.encode_place(location);
                stmts.extend(
                    self.encode_assign_operand(&encoded_loc, value)
                );
                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            }

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
                                            "unimplemented!" if second_def_site_span.contains("<unimplemented macros>") => PanicCause::Unimplemented,
                                            _ => PanicCause::Panic
                                        }
                                    } else {
                                        PanicCause::Panic
                                    }
                                }
                                _ => PanicCause::Unknown
                            }
                        } else {
                            // Something else called panic!()
                            PanicCause::Unknown
                        };
                        let pos = self.encoder.error_manager().register(
                            term.source_info.span,
                            ErrorCtxt::Panic(panic_cause)
                        );
                        stmts.push(vir::Stmt::Assert(false.into(), pos));
                    }

                    "<std::boxed::Box<T>>::new" => {
                        // This is the initialization of a box
                        // args[0]: value to put in the box
                        assert!(args.len() == 1);

                        let &(ref target_place, _) = destination.as_ref().unwrap();
                        let (dst, dest_ty, _) = self.encode_place(target_place);
                        let boxed_ty = dest_ty.boxed_ty();
                        let ref_field = self.encoder.encode_ref_field("val_ref", boxed_ty);

                        let box_content = vir::Place::Field(
                            box dst.clone(),
                            ref_field,
                        );

                        // Allocate `box_content`
                        stmts.extend(
                            self.encode_havoc_and_allocation(&box_content, boxed_ty)
                        );

                        // Initialize `box_content`
                        stmts.extend(
                            self.encode_assign_operand(&box_content, &args[0])
                        );
                    }

                    // generic function call
                    _ => {
                        let is_pure_function = self.encoder.env().has_attribute_name(def_id, "pure");
                        if is_pure_function {
                            let function_name = self.encoder.encode_pure_function_use(def_id);
                            debug!("Encoding pure function call '{}'", function_name);
                            assert!(destination.is_some());

                            let mut arg_exprs = Vec::new();
                            for operand in args.iter() {
                                let arg_expr = self.encode_operand_expr(operand);
                                arg_exprs.push(arg_expr);
                            }

                            let return_type = self.encoder.encode_pure_function_return_type(def_id);
                            let formal_args: Vec<vir::LocalVar> = args
                                .iter()
                                .enumerate()
                                .map(
                                    |(i, arg)|
                                        vir::LocalVar::new(
                                            format!("x{}", i),
                                            self.mir_encoder.encode_operand_expr_type(arg)
                                        )
                                ).collect();

                            let func_call = vir::Expr::func_app(
                                function_name,
                                arg_exprs,
                                formal_args,
                                return_type
                            );

                            // Havoc the lhs
                            let (target_place, target_ty, _) = match destination.as_ref() {
                                Some((ref dst, _)) => self.encode_place(dst),
                                None => unreachable!()
                            };
                            stmts.extend(
                                self.encode_havoc_and_allocation(&target_place, target_ty)
                            );

                            // Initialize the lhs
                            let target_value = match destination.as_ref() {
                                Some((ref dst, _)) => self.eval_place(dst),
                                None => unreachable!()
                            };
                            stmts.push(
                                vir::Stmt::Inhale(
                                    vir::Expr::eq_cmp(
                                        target_value.into(),
                                        func_call
                                    )
                                )
                            );

                        } else {
                            debug!("Encoding non-pure function call '{}'", func_proc_name);
                            let mut stmts_after: Vec<vir::Stmt> = vec![];
                            let mut arg_vars = Vec::new();
                            let mut encoded_args = Vec::new();

                            for operand in args.iter() {
                                let (arg_var, _, effects_before, effects_after) = self.encode_operand(operand);
                                arg_vars.push(arg_var);
                                encoded_args.push(self.encode_prusti_local(arg_var));
                                stmts.extend(effects_before);
                                stmts_after.extend(effects_after);
                            }

                            let mut encoded_target: vir::LocalVar;
                            let target = {
                                match destination.as_ref() {
                                    Some((ref target_place, _)) => {
                                        let (dst, ty, _) = self.encode_place(target_place);
                                        let local = self.locals.get_fresh(ty);
                                        encoded_target = self.encode_prusti_local(local);
                                        stmts_after.push(vir::Stmt::Assign(dst, encoded_target.clone().into(), vir::AssignKind::Move));
                                        local
                                    }
                                    None => {
                                        // The return type is Never
                                        // This means that the function call never returns
                                        // So, we `assume false` after the function call
                                        stmts_after.push(vir::Stmt::Inhale(vir::Const::Bool(false).into()));
                                        // Return a dummy local variable
                                        let never_ty = self.encoder.env().tcx().mk_ty(
                                            ty::TypeVariants::TyNever
                                        );
                                        let local = self.locals.get_fresh(never_ty);
                                        encoded_target = self.encode_prusti_local(local);
                                        local
                                    }
                                }
                            };

                            let procedure_contract = self.encoder
                                .get_procedure_contract_for_call(def_id, &arg_vars, target);

                            let label = self.cfg_method.get_fresh_label_name();
                            stmts.push(vir::Stmt::Label(label.clone()));

                            warn!("TODO: incomplete encoding of precondition of method call");
                            let (pre_type_spec, pre_func_spec) = self.encode_precondition_expr(&procedure_contract);
                            let pos = self.encoder.error_manager().register(
                                term.source_info.span,
                                ErrorCtxt::ExhalePrecondition
                            );
                            stmts.push(vir::Stmt::Assert(pre_func_spec, pos.clone()));
                            stmts.push(vir::Stmt::Exhale(pre_type_spec, pos));

                            let is_trusted = self.encoder.env()
                                .has_attribute_name(def_id, "trusted");

                            if is_trusted {
                                debug!("Encoding a trusted method call: {}", func_proc_name);
                                stmts.extend(
                                    self.encode_havoc(&encoded_target.into(), self.locals.get_type(target))
                                );
                            } else {
                                stmts.push(vir::Stmt::MethodCall(
                                    self.encoder.encode_procedure_use(def_id), // TODO
                                    vec![],
                                    vec![ encoded_target ],
                                ));
                            }

                            let (post_type_spec, post_func_spec) = self.encode_postcondition_expr(&procedure_contract, &label);
                            stmts.push(vir::Stmt::Inhale(post_type_spec));
                            stmts.push(vir::Stmt::Inhale(post_func_spec));

                            stmts.extend(stmts_after);
                        }
                    }
                }

                if let &Some((_, target)) = destination {
                    let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                    (stmts, Successor::Goto(*target_cfg_block))
                } else {
                    // Encode unreachability
                    stmts.push(
                        vir::Stmt::Inhale(false.into())
                    );
                    (stmts, Successor::Return)
                }
            }

            TerminatorKind::Call { .. } => {
                // Other kind of calls?
                unimplemented!();
            }

            TerminatorKind::Assert { ref cond, expected, ref target, ref msg, .. } => {
                trace!("Assert cond '{:?}', expected '{:?}'", cond, expected);
                let cond_val = self.encode_operand_expr(cond);
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
                        self.encoder.error_manager().register(
                            term.source_info.span,
                            ErrorCtxt::AssertTerminator(msg.description().to_string())
                        ),
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

    fn encode_place_predicate_body(&self, place: vir::Place) -> vir::Expr {
        let predicate_name = place.typed_ref_name().unwrap();
        let predicate = self.encoder.get_type_predicate_by_name(&predicate_name).unwrap();
        let pred_self_place: vir::Place = predicate.args[0].clone().into();
        predicate.body.unwrap().replace(&pred_self_place, &place)
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

    /// Encode the precondition with two expressions:
    /// - one for the type encoding
    /// - one for the functional specification.
    fn encode_precondition_expr(&self, contract: &ProcedureContract<'tcx>) -> (vir::Expr, vir::Expr) {
        let type_spec = contract.args.iter().map(|&local| self.encode_local_variable_permission(local));
        let mut func_spec: Vec<vir::Expr> = vec![];

        // Encode functional specification
        let encoded_args: Vec<vir::Expr> = contract.args.iter()
            .map(|local| self.encode_prusti_local(*local).into())
            .collect();
        let encoded_return: vir::Expr = self.encode_prusti_local(contract.returned_value).into();
        for item in contract.functional_precondition() {
            func_spec.push(self.encoder.encode_assertion(&item.assertion, &self.mir, &"", &encoded_args, &encoded_return, false));
        }

        (type_spec.into_iter().conjoin(), func_spec.into_iter().conjoin())
    }

    /// Encode precondition inhale on the definition side.
    fn encode_preconditions(&mut self, start_cfg_block: CfgBlockIndex,
                            contract: &ProcedureContract<'tcx>) {
        self.cfg_method.add_stmt(start_cfg_block, vir::Stmt::comment("Preconditions:"));
        let (type_spec, func_spec) = self.encode_precondition_expr(contract);
        self.cfg_method.add_stmt(start_cfg_block, vir::Stmt::Inhale(type_spec));
        self.cfg_method.add_stmt(start_cfg_block, vir::Stmt::Inhale(func_spec));
        self.cfg_method.add_stmt(start_cfg_block, vir::Stmt::Label(PRECONDITION_LABEL.to_string()));
    }

    /// Encode permissions that are implicitly carried by the given place.
    /// `state_label` – the label of the state in which the place should
    /// be evaluated (the place expression is wrapped in the labelled old).
    fn encode_place_permission(&self, place: &Place<'tcx>, state_label: Option<&str>, ) -> vir::Expr {
        let (mut encoded_place, place_ty, _) = self.encode_generic_place(place);
        let predicate_name = self.encoder.encode_type_predicate_use(place_ty);
        vir::Expr::PredicateAccessPredicate(
            box vir::Expr::PredicateAccess(
                predicate_name,
                vec![
                    if let Some(label) = state_label {
                        self.mir_encoder.encode_old_place(encoded_place, label)
                    } else {
                        encoded_place.into()
                    }
                ],
            ),
            vir::Perm::full(),
        )
    }

    /// Encode the postcondition with two expressions:
    /// - one for the type encoding
    /// - one for the functional specification.
    fn encode_postcondition_expr(&self, contract: &ProcedureContract<'tcx>,
                                 label: &str) -> (vir::Expr, vir::Expr) {
        let mut type_spec = Vec::new();
        for place in contract.returned_refs.iter() {
            debug!("Put permission {:?} in postcondition", place);
            type_spec.push(self.encode_place_permission(place, Some(label)));
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
            type_spec.push(vir::Expr::MagicWand(box lhs, box rhs));
        }
        type_spec.push(self.encode_local_variable_permission(contract.returned_value));

        // Encode functional specification
        let encoded_args: Vec<vir::Expr> = contract.args.iter()
            .map(|local| self.encode_prusti_local(*local).into())
            .collect();
        let encoded_return: vir::Expr = self.encode_prusti_local(contract.returned_value).into();
        let mut func_spec = Vec::new();
        for item in contract.functional_postcondition() {
            func_spec.push(self.encoder.encode_assertion(&item.assertion, &self.mir, label, &encoded_args, &encoded_return, false));
        }

        (type_spec.into_iter().conjoin(), func_spec.into_iter().conjoin())
    }

    /// Encode postcondition exhale on the definition side.
    fn encode_postconditions(&mut self, return_cfg_block: CfgBlockIndex,
                             contract: &ProcedureContract<'tcx>) {
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::comment("Postconditions:"));
        let (type_spec, func_spec) = self.encode_postcondition_expr(contract, PRECONDITION_LABEL);
        let pos = self.encoder.error_manager().register(
            // TODO: choose a better error span
            self.mir.span,
            ErrorCtxt::ExhalePostcondition
        );
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::Assert(func_spec, pos.clone()));

        /*
        // Require the deref of reference arguments to be folded (see issue #47)
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::comment(format!("Fold predicates for &mut args")));
        for arg_index in self.mir.args_iter() {
            let arg_ty = self.mir.local_decls[arg_index].ty;
            if self.mir_encoder.is_reference(arg_ty) {
                let encoded_arg = self.mir_encoder.encode_local(arg_index);
                let (deref_place, ..) = self.mir_encoder.encode_deref(encoded_arg.into(), arg_ty);
                let deref_pred = self.mir_encoder.encode_place_predicate_permission(deref_place).unwrap();
                self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::WeakObtain(deref_pred));
            }
        }
        */

        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::Exhale(type_spec, pos));
    }

    fn encode_loop_invariant_exhale(&mut self, loop_head: BasicBlockIndex, source: BasicBlockIndex) {
        let permissions_forest = self.loops.compute_loop_invariant(loop_head);
        debug!("permissions_forest: {:?}", permissions_forest);
        unimplemented!("TODO: encode exhale of loop invariant...");
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
                    }

                    ty::TypeVariants::TyAdt(ref adt_def, ref subst) if !adt_def.is_box() => {
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
                    }

                    ref x => unimplemented!("{:?}", x),
                }
            }

            &mir::ProjectionElem::Deref => {
                self.mir_encoder.encode_deref(encoded_base, base_ty)
            }

            &mir::ProjectionElem::Downcast(ref adt_def, variant_index) => {
                debug!("Downcast projection {:?}, {:?}", adt_def, variant_index);
                (encoded_base, base_ty, Some(variant_index))
            }

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
            }
            &Place::SubstitutedPlace { substituted_root, ref place } => {
                self.encode_place_with_subst_root(place, Some(substituted_root))
            }
        }
    }

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
    fn encode_operand_expr(&mut self, operand: &mir::Operand<'tcx>) -> vir::Expr {
        match operand {
            &mir::Operand::Constant(box mir::Constant { ty, literal: mir::Literal::Value { value }, .. }) => {
                self.encoder.encode_const_expr(value)
            }
            &mir::Operand::Copy(ref place) => {
                let val_place = self.eval_place(place);
                val_place.into()
            }
            &mir::Operand::Move(ref place) => {
                let (encoded_place, _, _) = self.encode_place(place);
                let val_place = self.eval_place(&place);
                val_place.into()
            }
            x => unimplemented!("{:?}", x)
        }
    }

    fn get_operand_ty(&mut self, operand: &mir::Operand<'tcx>) -> ty::Ty<'tcx> {
        debug!("Get operand ty {:?}", operand);
        match operand {
            &mir::Operand::Move(ref place) => {
                let (_, ty, _) = self.encode_place(place);
                ty
            }
            &mir::Operand::Copy(ref place) => {
                let (_, ty, _) = self.encode_place(place);
                ty
            }
            &mir::Operand::Constant(box mir::Constant { ty, .. }) => {
                ty
            }
        }
    }

    /// Return type:
    /// - `Vec<vir::Stmt>`: the statements that encode the assignment of `operand` to `lhs`
    fn encode_assign_operand(&mut self, lhs: &vir::Place, operand: &mir::Operand<'tcx>) -> Vec<vir::Stmt> {
        debug!("Encode assign operand {:?}", operand);
        match operand {
            &mir::Operand::Move(ref place) => {
                let (src, ty, _) = self.encode_place(place);
                // Move the values from `src` to `lhs`
                vec![
                    vir::Stmt::Assign(lhs.clone(), src.clone().into(), vir::AssignKind::Move)
                ]
            }

            &mir::Operand::Copy(ref place) => {
                let (src, ty, _) = self.encode_place(place);
                // Copy the values from `src` to `lhs`
                self.encode_copy(src, lhs.clone(), ty, false)
            }

            &mir::Operand::Constant(box mir::Constant { ty, ref literal, .. }) => {
                let mut stmts = Vec::new();
                // Initialize the constant
                match literal {
                    mir::Literal::Value { value } => {
                        let const_val = self.encoder.encode_const_expr(value);
                        let field = self.encoder.encode_value_field(ty);
                        // Initialize value of lhs
                        stmts.push(
                            vir::Stmt::Assign(lhs.clone().access(field), const_val, vir::AssignKind::Copy)
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
            }
        }
    }

    #[deprecated(note="please use `encode_assign_operand` instead")]
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
                let stmt_before = vir::Stmt::Assign(viper_local.clone().into(), src.clone().into(), vir::AssignKind::Move);
                (local, viper_local, vec![stmt_before], vec![])
            }
            &mir::Operand::Copy(ref place) => {
                let (src, ty, _) = self.encode_place(place);
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                let mut stmts: Vec<vir::Stmt> = vec![];
                // Before, copy the values from src to viper_local
                stmts.extend(
                    self.encode_copy(src, viper_local.clone().into(), ty, false)
                );
                (local, viper_local, stmts, vec![])
            }
            &mir::Operand::Constant(box mir::Constant { ty, ref literal, .. }) => {
                let local = self.locals.get_fresh(ty);
                let viper_local = self.encode_prusti_local(local);
                let mut stmts = Vec::new();
                let field = self.encoder.encode_value_field(ty);
                // Evaluate the constant
                /* TODO: in the future use the following commented code (not exposed by the compiler)
                let tcx = self.encoder.env().tcx();
                let const_prop = ConstPropagator::new(self.mir, tcx, MirSource::item(self.proc_def_id));
                let evaluated_const = const_prop.eval_constant(constant);
                let const_val = self.encoder.encode_const_expr(value);
                */
                match literal {
                    mir::Literal::Value { value } => {
                        let const_val = self.encoder.encode_const_expr(value);
                        // Before, initialize viper_local
                        stmts.push(
                            vir::Stmt::Assign(vir::Place::from(viper_local.clone()).access(field), const_val, vir::AssignKind::Copy)
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
                        let const_val = self.encoder.encode_const_expr(value);
                        */
                    }
                }
                (local, viper_local, stmts, vec![])
            }
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
                vir::Stmt::Assign(dst.clone().into(), tmp_var.into(), vir::AssignKind::Move),
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

    /// Encodes the copy of a structure, reading from a source `src` and using `dst` as target.
    /// The copy is neither shallow or deep:
    /// - if a field encodes a Rust reference, the reference is copied (shallow copy);
    /// - if a field does not encode a Rust reference, but is a Viper reference, a recursive call
    ///   copies the content of the field (deep copy).
    /// - if a field does not encode a Rust reference and is not a Viper reference, the field is
    ///   copied.
    ///
    /// The `is_move` parameter is used just to assert that a reference is only copied when encoding
    /// a Rust move assignment, and not a copy assignment.
    fn encode_copy(&mut self, src: vir::Place, dst: vir::Place, self_ty: ty::Ty<'tcx>, is_move: bool) -> Vec<vir::Stmt> {
        debug!("Encode copy {:?}, {:?}, {:?}", src, dst, self_ty);

        match self_ty.sty {
            ty::TypeVariants::TyBool |
            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) => {
                let field = self.encoder.encode_value_field(self_ty);
                vec![
                    // Copy value
                    vir::Stmt::Assign(
                        dst.clone().access(field.clone()),
                        src.clone().access(field.clone()).into(),
                        vir::AssignKind::Copy
                    )
                ]
            }

            ty::TypeVariants::TyTuple(elems) => {
                let mut stmts: Vec<vir::Stmt> = vec![];
                for (field_num, ty) in elems.iter().enumerate() {
                    let field_name = format!("tuple_{}", field_num);
                    let field = self.encoder.encode_ref_field(&field_name, ty);
                    stmts.extend(
                        // Copy fields
                        self.encode_copy(
                            src.clone().access(field.clone()),
                            dst.clone().access(field.clone()),
                            ty,
                            is_move
                        )
                    );
                }
                stmts
            }

            ty::TypeVariants::TyAdt(ref adt_def, ref subst) if !adt_def.is_box() => {
                let mut stmts: Vec<vir::Stmt> = vec![];
                let num_variants = adt_def.variants.len();
                let discriminant_field = self.encoder.encode_discriminant_field();
                if num_variants > 1 {
                    stmts.push(
                        // Copy discriminant
                        vir::Stmt::Assign(
                            dst.clone().access(discriminant_field.clone()),
                            src.clone().access(discriminant_field.clone()).into(),
                            vir::AssignKind::Copy
                        )
                    );
                }
                let tcx = self.encoder.env().tcx();
                for (variant_index, variant_def) in adt_def.variants.iter().enumerate() {
                    for field in &variant_def.fields {
                        let field_name = format!("enum_{}_{}", variant_index, field.ident.as_str());
                        let field_ty = field.ty(tcx, subst);
                        let elem_field = self.encoder.encode_ref_field(&field_name, field_ty);
                        stmts.extend(
                            // Copy fields
                            self.encode_copy(
                                src.clone().access(elem_field.clone()),
                                dst.clone().access(elem_field.clone()),
                                field_ty,
                                is_move
                            )
                        )
                    }
                }
                stmts
            }

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty, .. }) |
            ty::TypeVariants::TyRef(_, ty, _) => {
                // Ensure that we are encoding a move, not a copy (enforced byt the Rust typesystem)
                assert!(is_move);
                let ref_field = self.encoder.encode_ref_field("val_ref", ty);
                vec![
                    // Move the reference to the boxed value
                    vir::Stmt::Assign(
                        dst.clone().access(ref_field.clone()),
                        src.clone().access(ref_field.clone()).into(),
                        vir::AssignKind::Move
                    )
                ]
            }

            ty::TypeVariants::TyAdt(ref adt_def, ref subst) if adt_def.is_box() => {
                // Ensure that we are encoding a move, not a copy (enforced byt the Rust typesystem)
                assert!(is_move);
                let field_ty = self_ty.boxed_ty();
                let ref_field = self.encoder.encode_ref_field("val_ref", field_ty);
                assert_eq!(adt_def.variants.len(), 1);
                vec![
                    // Move the reference to the boxed value
                    vir::Stmt::Assign(
                        dst.clone().access(ref_field.clone()),
                        src.clone().access(ref_field.clone()).into(),
                        vir::AssignKind::Move
                    )
                ]
            }

            ref x => unimplemented!("{:?}", x),
        }
    }

    fn encode_bin_op_expr(&mut self, op: mir::BinOp, left: vir::Expr, right: vir::Expr, ty: ty::Ty<'tcx>) -> vir::Expr {
        let is_bool = ty.sty == ty::TypeVariants::TyBool;
        match op {
            mir::BinOp::Eq => vir::Expr::eq_cmp(left, right),
            mir::BinOp::Ne => vir::Expr::ne_cmp(left, right),
            mir::BinOp::Gt => vir::Expr::gt_cmp(left, right),
            mir::BinOp::Ge => vir::Expr::ge_cmp(left, right),
            mir::BinOp::Lt => vir::Expr::lt_cmp(left, right),
            mir::BinOp::Le => vir::Expr::le_cmp(left, right),
            mir::BinOp::Add => vir::Expr::add(left, right),
            mir::BinOp::Sub => vir::Expr::sub(left, right),
            mir::BinOp::Rem => vir::Expr::rem(left, right),
            mir::BinOp::Div => vir::Expr::div(left, right),
            mir::BinOp::Mul => vir::Expr::mul(left, right),
            mir::BinOp::BitAnd if is_bool => vir::Expr::and(left, right),
            mir::BinOp::BitOr if is_bool => vir::Expr::or(left, right),
            mir::BinOp::BitXor if is_bool => vir::Expr::xor(left, right),
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_unary_op_expr(&mut self, op: mir::UnOp, expr: vir::Expr) -> vir::Expr {
        match op {
            mir::UnOp::Not => vir::Expr::not(expr),
            mir::UnOp::Neg => vir::Expr::minus(expr),
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
        operands: &Vec<mir::Operand<'tcx>>,
    ) -> Vec<vir::Stmt> {
        debug!("Encode aggregate {:?}, {:?}", aggregate, operands);
        let mut stmts: Vec<vir::Stmt> = vec![];
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
            }

            &mir::AggregateKind::Adt(adt_def, variant_index, subst, _) => {
                let num_variants = adt_def.variants.len();
                if num_variants > 1 {
                    let discr_field = self.encoder.encode_discriminant_field();
                    stmts.push(
                        vir::Stmt::Assign(
                            dst.clone().access(discr_field).into(),
                            variant_index.into(),
                            vir::AssignKind::Copy
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
            }

            ref x => unimplemented!("{:?}", x)
        }
    }
}
