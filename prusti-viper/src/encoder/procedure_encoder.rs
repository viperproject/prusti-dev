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
use encoder::vir::{Zero, One};
use encoder::vir::ExprIterator;
use prusti_interface::config;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::BasicBlockIndex;
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;
use prusti_interface::environment::PermissionKind;
use prusti_interface::environment::polonius_info::{LoanPlaces, PoloniusInfo};
use prusti_interface::environment::polonius_info::{ReborrowingZombity, ReborrowingGuard, ReborrowingDAGNode, ReborrowingForest, ReborrowingTree, ReborrowingNode, ReborrowingKind, ReborrowingBranching};
use prusti_interface::environment::borrowck::{facts};
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
use prusti_interface::utils::get_attr_value;

pub struct ProcedureEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: ProcedureDefId,
    procedure: &'p Procedure<'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    cfg_method: vir::CfgMethod,
    locals: LocalVariableManager<'tcx>,
    loop_encoder: LoopEncoder<'p, 'tcx>,
    auxiliar_local_vars: HashMap<String, vir::Type>,
    mir_encoder: MirEncoder<'p, 'v, 'r, 'a, 'tcx>,
    check_panics: bool,
    polonius_info: PoloniusInfo<'p, 'tcx>,
    label_after_location: HashMap<mir::Location, String>,
    /// Contains the boolean local variables that became `true` the first time the block is executed
    cfg_block_has_been_executed: HashMap<mir::BasicBlock, vir::LocalVar>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> ProcedureEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, procedure: &'p Procedure<'a, 'tcx>) -> Self {
        debug!("ProcedureEncoder constructor");

        let mir = procedure.get_mir();
        let def_id = procedure.get_id();
        let tcx = encoder.env().tcx();

        let cfg_method = vir::CfgMethod::new(
            // method name
            encoder.encode_item_name(def_id),
            // formal args
            vec![],
            // formal returns
            vec![],
            // local vars
            vec![],
            // reserved labels
            vec![],
        );

        ProcedureEncoder {
            encoder,
            proc_def_id: def_id,
            procedure,
            mir,
            cfg_method,
            locals: LocalVariableManager::new(&mir.local_decls),
            loop_encoder: LoopEncoder::new(mir, tcx, def_id),
            auxiliar_local_vars: HashMap::new(),
            mir_encoder: MirEncoder::new(encoder, mir, def_id),
            check_panics: config::check_panics(),
            polonius_info: PoloniusInfo::new(tcx, def_id, mir),
            label_after_location: HashMap::new(),
            cfg_block_has_been_executed: HashMap::new(),
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
            let name = self.mir_encoder.encode_local_var_name(local);
            let type_name = self.encoder.encode_type_predicate_use(self.mir_encoder.get_local_ty(local));
            self.cfg_method.add_formal_return(&name, vir::Type::TypedRef(type_name))
        }

        let mut cfg_blocks: HashMap<BasicBlockIndex, CfgBlockIndex> = HashMap::new();

        // Initialize CFG blocks
        let start_cfg_block = self.cfg_method.add_block("start", vec![], vec![
            vir::Stmt::comment(format!("========== start =========="))
        ]);

        for bbi in self.procedure.get_reachable_cfg_blocks() {
            let cfg_block = self.cfg_method.add_block(&format!("{:?}", bbi), vec![], vec![
                vir::Stmt::comment(format!("========== {:?} ==========", bbi))
            ]);
            cfg_blocks.insert(bbi, cfg_block);
        }

        // Set the first CFG block
        self.cfg_method.set_successor(
            start_cfg_block,
            Successor::Goto(cfg_blocks[&self.procedure.get_first_cfg_block()])
        );

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
        for bbi in self.procedure.get_reachable_cfg_blocks() {
            let bb_data = &self.mir.basic_blocks()[bbi];
            let statements: &Vec<mir::Statement<'tcx>> = &bb_data.statements;
            let cfg_block = *cfg_blocks.get(&bbi).unwrap();

            // Store a flag that becomes true the first time the block is executed
            let executed_flag_var = self.cfg_method.add_fresh_local_var(vir::Type::Bool);
            self.cfg_method.add_stmt(
                start_cfg_block,
                vir::Stmt::Assign(vir::Place::Base(executed_flag_var.clone()), false.into(), vir::AssignKind::Copy)
            );
            self.cfg_method.add_stmt(
                cfg_block,
                vir::Stmt::Assign(vir::Place::Base(executed_flag_var.clone()), true.into(), vir::AssignKind::Copy)
            );
            self.cfg_block_has_been_executed.insert(bbi, executed_flag_var);

            // Inhale the loop invariant if this is a loop head
            if self.loop_encoder.is_loop_head(bbi) {
                let stmts = self.encode_loop_invariant_inhale(bbi);
                for stmt in stmts.into_iter() {
                    self.cfg_method.add_stmt(cfg_block, stmt);
                }
            }

            // Add an `EndFrame` statement if the incoming edge is an *out* edge from a loop
            let predecessors = self.procedure.predecessors(bbi);
            let predecessor_count = predecessors.len();
            for &predecessor in predecessors.iter() {
                let is_edge_out_loop = self.loop_encoder.get_loop_depth(predecessor) > self.loop_encoder.get_loop_depth(bbi);
                if is_edge_out_loop {
                    assert!(predecessor_count == 1); // FIXME: this is a bug. See issue #58
                    let loop_head = self.loop_encoder.get_loop_head(predecessor).unwrap();
                    let stmts = self.encode_loop_invariant_obtain(loop_head);
                    for stmt in stmts.into_iter() {
                        self.cfg_method.add_stmt(cfg_block, stmt);
                    }
                    self.cfg_method.add_stmt(cfg_block, vir::Stmt::EndFrame);
                }
            }

            // Encode statements of the block, if this is not a "spec" block
            if !self.procedure.is_spec_block(bbi) {
                for (stmt_index, stmt) in statements.iter().enumerate() {
                    trace!("Encode statement {:?}:{}", bbi, stmt_index);
                    self.cfg_method.add_stmt(cfg_block, vir::Stmt::comment(format!("[mir] {:?}", stmt)));
                    let location = mir::Location {
                        block: bbi,
                        statement_index: stmt_index
                    };
                    if location.statement_index == 0 {
                        for stmt in self.encode_expiring_borrows_before(location).drain(..) {
                            self.cfg_method.add_stmt(cfg_block, stmt);
                        }
                    }
                    for stmt in self.encode_statement(stmt, location).drain(..) {
                        self.cfg_method.add_stmt(cfg_block, stmt);
                    }
                    for stmt in self.encode_expiring_borrows_at(location).drain(..) {
                        self.cfg_method.add_stmt(cfg_block, stmt);
                    }
                }
            } else {
                // Any spec block must be unreachable
                let pos = self.encoder.error_manager().register(
                    // TODO: choose a better error span
                    self.mir.span,
                    ErrorCtxt::Unexpected
                );
                self.cfg_method.add_stmt(
                    cfg_block,
                    vir::Stmt::comment("Unreachable block, used for type-checking specifications")
                );
                self.cfg_method.add_stmt(
                    cfg_block,
                    vir::Stmt::Assert(false.into(), pos)
                );
            }

            // Encode terminators and set CFG edges
            if let Some(ref term) = bb_data.terminator {
                trace!("Encode terminator of {:?}", bbi);
                let cfg_block = *cfg_blocks.get(&bbi).unwrap();
                self.cfg_method.add_stmt(cfg_block, vir::Stmt::comment(format!("[mir] {:?}", term.kind)));
                let location = mir::Location {
                    block: bbi,
                    statement_index: bb_data.statements.len()
                };
                if location.statement_index == 0 {
                    for stmt in self.encode_expiring_borrows_before(location).drain(..) {
                        self.cfg_method.add_stmt(cfg_block, stmt);
                    }
                }
                let (stmts, successor) = self.encode_terminator(
                    term,
                    location,
                    &cfg_blocks,
                    return_cfg_block,
                );
                for stmt in stmts.into_iter() {
                    self.cfg_method.add_stmt(cfg_block, stmt);
                }
                if successor != vir::Successor::Return {
                    for stmt in self.encode_expiring_borrows_at(location).drain(..) {
                        self.cfg_method.add_stmt(cfg_block, stmt);
                    }
                }
                self.cfg_method.set_successor(cfg_block, successor);
            }

            // Exhale the loop invariant if the successor is a loop head
            // Add an `BeginFrame` statement if the outgoing edge is an *in* edge
            let successor_count = bb_data.terminator().successors().count();
            for &successor in bb_data.terminator().successors() {
                if self.loop_encoder.is_loop_head(successor) {
                    assert!(successor_count == 1); // FIXME: this is a bug. See issue #58
                    let after_loop_iteration = self.loop_encoder.get_loop_head(bbi) == Some(successor);
                    let stmts = self.encode_loop_invariant_exhale(successor, after_loop_iteration);
                    for stmt in stmts.into_iter() {
                        self.cfg_method.add_stmt(cfg_block, stmt);
                    }
                    let is_edge_in_loop = self.loop_encoder.get_loop_depth(successor) > self.loop_encoder.get_loop_depth(bbi);
                    if is_edge_in_loop {
                        self.cfg_method.add_stmt(cfg_block, vir::Stmt::BeginFrame);
                    }
                }
            }
        }

        let local_vars: Vec<_> = self.locals
            .iter()
            .filter(|local| !self.locals.is_return(*local))
            .collect();
        for local in local_vars.iter() {
            let local_ty = self.locals.get_type(*local);
            if let ty::TypeVariants::TyClosure(..) = local_ty.sty {
                // Do not encode closures
                continue;
            }
            let type_name = self.encoder.encode_type_predicate_use(local_ty);
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
            let local_ty = self.locals.get_type(*local);
            if let ty::TypeVariants::TyClosure(..) = local_ty.sty {
                // Do not encode closures
                continue;
            }
            let type_name = self.encoder.encode_type_predicate_use(local_ty);
            let var_name = self.locals.get_name(*local);
            let var_type = vir::Type::TypedRef(type_name.clone());
            let local_var = vir::LocalVar::new(var_name.clone(), var_type);
            let alloc_stmt = vir::Stmt::Inhale(
                self.mir_encoder.encode_place_predicate_permission(local_var.clone().into(), vir::Frac::one()).unwrap()
            );
            self.cfg_method.add_stmt(start_cfg_block, alloc_stmt);
        }

        // Keep a copy of the value of the variable (fixes issue #20)
        let formal_args: Vec<_> = self.locals
            .iter()
            .filter(|local| self.locals.is_formal_arg(self.mir, *local))
            .collect();
        for local in formal_args.iter() {
            let local_ty = self.locals.get_type(*local);
            if let ty::TypeVariants::TyClosure(..) = local_ty.sty {
                // Do not encode closures
                continue;
            }
            let type_name = self.encoder.encode_type_predicate_use(local_ty);
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
            let local_var = self.mir_encoder.encode_local(local);
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
                            // See issue #20 "Evaluation of arguments in old expressions"
                            warn!("TODO: local variables may be evaluated in the wrong state");
                            old_expr
                        }
                    }
                )
            );
        }

        let method_name = self.cfg_method.name();

        self.encoder.log_vir_program_before_foldunfold(self.cfg_method.to_string());

        // Dump initial CFG
        let source_path = self.encoder.env().source_path();
        let source_filename = source_path.file_name().unwrap().to_str().unwrap();
        Log::report_with_writer("graphviz_method_before_foldunfold", format!("{}.{}.dot", source_filename, method_name), |writer| self.cfg_method.to_graphviz(writer));

        // Add fold/unfold
        let final_method = foldunfold::add_fold_unfold(self.encoder, self.cfg_method);

        // Dump final CFG
        Log::report_with_writer("graphviz_method_before_viper", format!("{}.{}.dot", source_filename, method_name), |writer| final_method.to_graphviz(writer));

        final_method
    }

    fn encode_statement(&mut self, stmt: &mir::Statement<'tcx>, location: mir::Location) -> Vec<vir::Stmt> {
        debug!("Encode statement '{:?}', span: {:?}", stmt.kind, stmt.source_info.span);
        let mut stmts: Vec<vir::Stmt> = vec![];

        match stmt.kind {
            mir::StatementKind::StorageDead(_) |
            mir::StatementKind::StorageLive(_) |
            mir::StatementKind::EndRegion(_) |
            mir::StatementKind::ReadForMatch(_) |
            mir::StatementKind::Nop => stmts,

            mir::StatementKind::Assign(ref lhs, ref rhs) => {
                let (encoded_lhs, ty, _) = self.mir_encoder.encode_place(lhs);
                let type_name = self.encoder.encode_type_predicate_use(ty);
                match rhs {
                    &mir::Rvalue::Use(ref operand) => {
                        stmts.extend(
                            self.encode_assign_operand(&encoded_lhs, operand, location)
                        );
                        stmts
                    }

                    &mir::Rvalue::Aggregate(ref aggregate, ref operands) => {
                        stmts.extend(
                            self.encode_assign_aggregate(&encoded_lhs, ty, aggregate, operands, location)
                        );
                        stmts
                    }

                    &mir::Rvalue::BinaryOp(op, ref left, ref right) => {
                        let encoded_left = self.mir_encoder.encode_operand_expr(left);
                        let encoded_right = self.mir_encoder.encode_operand_expr(right);
                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.mir_encoder.encode_bin_op_expr(op, encoded_left, encoded_right, ty);
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
                        let encoded_left = self.mir_encoder.encode_operand_expr(left);
                        let encoded_right = self.mir_encoder.encode_operand_expr(right);
                        let encoded_value = self.mir_encoder.encode_bin_op_expr(op, encoded_left.clone(), encoded_right.clone(), ty);
                        let encoded_check = self.mir_encoder.encode_bin_op_check(op, encoded_left, encoded_right);
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
                        let encoded_val = self.mir_encoder.encode_operand_expr(operand);
                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.mir_encoder.encode_unary_op_expr(op, encoded_val);
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
                        let (encoded_src, src_ty, _) = self.mir_encoder.encode_place(src);
                        match src_ty.sty {
                            ty::TypeVariants::TyAdt(ref adt_def, _) if !adt_def.is_box() => {
                                let num_variants = adt_def.variants.len();
                                // Initialize `lhs.int_field`
                                let discr_field = self.encoder.encode_discriminant_field();
                                let discr_value: vir::Expr = if num_variants <= 1 {
                                    0.into()
                                } else {
                                    self.translate_maybe_borrowed_place(
                                        location,
                                        encoded_src.access(discr_field)
                                    ).into()
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
                                let discr_value: vir::Expr = self.translate_maybe_borrowed_place(
                                    location,
                                    encoded_src.access(value_field)
                                ).into();
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

                    &mir::Rvalue::Ref(ref _region, _, ref place) => {
                        let ref_field = self.encoder.encode_value_field(ty);
                        let (encoded_value, _, _) = self.mir_encoder.encode_place(place);
                        // Initialize ref_var.ref_field
                        stmts.push(
                            vir::Stmt::Assign(
                                encoded_lhs.clone().access(ref_field),
                                encoded_value.into(),
                                vir::AssignKind::MutableBorrow
                            )
                        );
                        // Store a label for this state
                        let label = self.cfg_method.get_fresh_label_name();
                        debug!("Current loc {:?} has label {}", location, label);
                        self.label_after_location.insert(location, label.clone());
                        stmts.push(vir::Stmt::Label(label.clone()));
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

    /// Translate a borrowed place to a place that is currently usable
    fn translate_maybe_borrowed_place(&self, location: mir::Location, place: vir::Place) -> vir::Place {
        let (all_active_loans, _) = self.polonius_info.get_all_active_loans(location);
        let relevant_active_loan_places: Vec<_> = all_active_loans
            .iter()
            .flat_map(|p| self.polonius_info.get_loan_places(p))
            .filter(|loan_places| {
                let (_, _, encoded_source) = self.encode_loan_places(loan_places);
                place.has_prefix(&encoded_source)
            })
            .collect();
        assert!(relevant_active_loan_places.len() <= 1);
        if !relevant_active_loan_places.is_empty() {
            let loan_places = &relevant_active_loan_places[0];
            let (encoded_dest, _, encoded_source) = self.encode_loan_places(loan_places);
            // Recursive translation
            self.translate_maybe_borrowed_place(
                loan_places.location,
                place.replace_prefix(&encoded_source, encoded_dest)
            )
        } else {
            place
        }
    }

    /// Encode the lhs and the rhs of the assignment that create the loan
    fn encode_loan_places(&self, loan_places: &LoanPlaces<'tcx>) -> (vir::Place, ty::Ty<'tcx>, vir::Place) {
        debug!("encode_loan_rvalue '{:?}'", loan_places);
        let (expiring_base, expiring_ty, _) = self.mir_encoder.encode_place(&loan_places.dest);
        match loan_places.source {
            mir::Rvalue::Ref(_, _, ref rhs_place) => {
                let (restored, _, _) = self.mir_encoder.encode_place(&rhs_place);
                let ref_field = self.encoder.encode_value_field(expiring_ty);
                let expiring = expiring_base.clone().access(ref_field);
                assert_eq!(expiring.get_type(), restored.get_type());
                (expiring, expiring_ty, restored)
            }

            mir::Rvalue::Use(mir::Operand::Move(ref rhs_place)) => {
                let (restored, _, _) = self.mir_encoder.encode_place(&rhs_place);
                let expiring = expiring_base;
                assert_eq!(expiring.get_type(), restored.get_type());
                (expiring, expiring_ty, restored)
            }

            ref x => unreachable!("Borrow restores rvalue {:?}", x)
        }
    }

    fn encode_expiration_of_reborrowing_dag_node(&mut self, node: &ReborrowingDAGNode) -> Vec<vir::Stmt> {
        trace!("encode_expiration_of_reborrowing_dag_node '{:?}'", node);
        let mut stmts: Vec<vir::Stmt> = vec![];

        match node.kind {
            ReborrowingKind::Assignment { ref loan } => {
                let loan_location = self.polonius_info.get_loan_location(&loan);
                let loan_places = self.polonius_info.get_loan_places(&loan).unwrap();
                //trace!("loan_places '{:?}'", loan_places);
                let (expiring, expiring_ty, restored) = self.encode_loan_places(&loan_places);
                //trace!("expiring '{:?}' restored '{:?}'", expiring, restored);
                let lhs_place = if node.incoming_zombies {
                    let lhs_label = self.label_after_location.get(&loan_location).expect(
                        &format!(
                            "No label has been saved for location {:?} ({:?})",
                            loan_location,
                            self.label_after_location
                        )
                    );
                    vir::LabelledPlace::old(expiring.clone(), lhs_label.clone())
                } else {
                    vir::LabelledPlace::curr(expiring.clone())
                };
                let rhs_place = match node.zombity {
                    ReborrowingZombity::Real => {
                        vir::LabelledPlace::curr(restored)
                    }

                    ReborrowingZombity::Zombie(rhs_location) => {
                        let rhs_label = self.label_after_location.get(&rhs_location).expect(
                            &format!(
                                "No label has been saved for location {:?} ({:?})",
                                rhs_location,
                                self.label_after_location
                            )
                        );
                        vir::LabelledPlace::old(restored.clone(), rhs_label.clone())
                    }
                };

                match node.guard {
                    ReborrowingGuard::NoGuard => {
                        stmts.push(
                            vir::Stmt::ExpireBorrow(lhs_place, rhs_place)
                        );
                    }

                    ReborrowingGuard::MirBlock(ref guard_bbi) => {
                        let executed_flag_var = &self.cfg_block_has_been_executed[guard_bbi];
                        stmts.push(
                            vir::Stmt::ExpireBorrowsIf(
                                vir::Place::Base(executed_flag_var.clone()).into(),
                                vec![
                                    vir::Stmt::ExpireBorrow(lhs_place, rhs_place)
                                ],
                                vec![]
                            )
                        );
                    }
                }

                // Apply the following (expensive) encoding only if we are in a loop
                if self.loop_encoder.get_loop_depth(loan_location.block) > 0 {
                    // When we restore a loan in a loop body, we want to have the permission
                    // on the borrowed thing because it may be go in the loop invariant that
                    // encodes *allocation*, not definedness
                    if !node.incoming_zombies {
                        stmts.extend(
                            self.encode_havoc_and_allocation(&expiring, expiring_ty)
                        );
                    }
                }
            }

            ReborrowingKind::Call { .. } => {
                unimplemented!("TODO: handle magic wand(s) obtained from function calls");
            }

            ReborrowingKind::Loop { .. } => {
                unimplemented!("TODO: handle magic wand(s) obtained from loops");
            }
        }

        stmts
    }

    fn encode_expiration_of_loans(&mut self, loans: Vec<facts::Loan>,
                                  zombie_loans: &[facts::Loan], location: mir::Location) -> Vec<vir::Stmt> {
        trace!("encode_expiration_of_loans '{:?}' '{:?}'", loans, zombie_loans);
        let mut stmts: Vec<vir::Stmt> = vec![];

        let reborrowing_dag = self.polonius_info.construct_reborrowing_dag(&loans, &zombie_loans, location);
        for node in reborrowing_dag.iter() {
            stmts.extend(
                self.encode_expiration_of_reborrowing_dag_node(node)
            )
        }

        if stmts.len() > 0 {
            stmts.insert(
                0,
                vir::Stmt::comment(format!("Expire {} dying loans", stmts.len()))
            );
            stmts.push(
                vir::Stmt::StopExpiringBorrows
            );
        }

        stmts
    }

    fn encode_expiring_borrows_before(&mut self, location: mir::Location) -> Vec<vir::Stmt> {
        debug!("encode_expiring_borrows_before '{:?}'", location);
        let (all_dying_loans, zombie_loans) = self.polonius_info.get_all_loans_dying_before(location);
        self.encode_expiration_of_loans(all_dying_loans, &zombie_loans, location)
    }

    fn encode_expiring_borrows_at(&mut self, location: mir::Location) -> Vec<vir::Stmt> {
        debug!("encode_expiring_borrows_at '{:?}'", location);
        let (all_dying_loans, zombie_loans) = self.polonius_info.get_all_loans_dying_at(location);
        self.encode_expiration_of_loans(all_dying_loans, &zombie_loans, location)
    }

    fn encode_terminator(&mut self, term: &mir::Terminator<'tcx>, location: mir::Location,
                         cfg_blocks: &HashMap<BasicBlockIndex, CfgBlockIndex>,
                         return_cfg_block: CfgBlockIndex) -> (Vec<vir::Stmt>, Successor) {
        debug!("Encode terminator '{:?}', span: {:?}", term.kind, term.source_info.span);
        let mut stmts: Vec<vir::Stmt> = vec![];

        match term.kind {
            TerminatorKind::Return => {
                (stmts, Successor::Goto(return_cfg_block))
            }

            TerminatorKind::Goto { target } => {
                let target_cfg_block = cfg_blocks.get(&target).unwrap();
                (stmts, Successor::Goto(*target_cfg_block))
            }

            TerminatorKind::SwitchInt { ref targets, ref discr, ref values, switch_ty } => {
                trace!("SwitchInt ty '{:?}', discr '{:?}', values '{:?}'", switch_ty, discr, values);
                let mut cfg_targets: Vec<(vir::Expr, CfgBlockIndex)> = vec![];

                // Use a local variable for the discriminant (see issue #57)
                let discr_var = match switch_ty.sty {
                    ty::TypeVariants::TyBool => {
                        self.cfg_method.add_fresh_local_var(vir::Type::Bool)
                    }

                    ty::TypeVariants::TyInt(_) |
                    ty::TypeVariants::TyUint(_) => {
                        self.cfg_method.add_fresh_local_var(vir::Type::Int)
                    }

                    ref x => unreachable!("{:?}", x)
                };
                let encoded_discr = self.mir_encoder.encode_operand_expr(discr);
                stmts.push(
                    vir::Stmt::Assign(
                        discr_var.clone().into(),
                        match encoded_discr.as_place() {
                            Some(discr_place) => self.translate_maybe_borrowed_place(location, discr_place).into(),
                            None => encoded_discr
                        },
                        vir::AssignKind::Copy
                    )
                );

                for (i, &value) in values.iter().enumerate() {
                    let target = targets[i as usize];
                    // Convert int to bool, if required
                    let viper_guard = match switch_ty.sty {
                        ty::TypeVariants::TyBool => {
                            if value == 0 {
                                // If discr is 0 (false)
                                vir::Expr::not(discr_var.clone().into())
                            } else {
                                // If discr is not 0 (true)
                                discr_var.clone().into()
                            }
                        }

                        ty::TypeVariants::TyInt(_) |
                        ty::TypeVariants::TyUint(_) => {
                            vir::Expr::eq_cmp(
                                discr_var.clone().into(),
                                self.encoder.encode_int_cast(value, switch_ty)
                            )
                        }

                        ref x => unreachable!("{:?}", x)
                    };
                    let target_cfg_block = cfg_blocks.get(&target).unwrap();
                    cfg_targets.push((viper_guard, *target_cfg_block))
                }
                let default_target = targets[values.len()];
                let cfg_default_target = if let Some(cfg_target) = cfg_blocks.get(&default_target) {
                    *cfg_target
                } else {
                    // Prepare a block that encodes the unreachable branch
                    assert!(
                        if let mir::TerminatorKind::Unreachable = self.mir[default_target].terminator.as_ref().unwrap().kind {
                            true
                        } else {
                            false
                        }
                    );
                    let unreachable_label = self.cfg_method.get_fresh_label_name();
                    let unreachable_block = self.cfg_method.add_block(&unreachable_label, vec![], vec![
                        vir::Stmt::comment(format!("========== {} ==========", &unreachable_label)),
                        vir::Stmt::comment(format!("Block marked as 'unreachable' by the compiler")),
                    ]);
                    if config::check_unreachable_terminators() {
                        let pos = self.encoder.error_manager().register(
                            term.source_info.span,
                            ErrorCtxt::UnreachableTerminator
                        );
                        self.cfg_method.add_stmt(
                            unreachable_block,
                            vir::Stmt::Assert(false.into(), pos)
                        );
                    }
                    self.cfg_method.set_successor(unreachable_block, Successor::Return);
                    unreachable_block
                };

                (stmts, Successor::GotoSwitch(cfg_targets, cfg_default_target))
            }

            TerminatorKind::Unreachable => unreachable!(),

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
                let target_cfg_block = cfg_blocks.get(&target).unwrap();
                (stmts, Successor::Goto(*target_cfg_block))
            }

            TerminatorKind::FalseEdges { ref real_target, .. } => {
                let target_cfg_block = cfg_blocks.get(&real_target).unwrap();
                (stmts, Successor::Goto(*target_cfg_block))
            }

            TerminatorKind::FalseUnwind { real_target, .. } => {
                let target_cfg_block = cfg_blocks.get(&real_target).unwrap();
                (stmts, Successor::Goto(*target_cfg_block))
            }

            TerminatorKind::DropAndReplace { ref target, location: ref lhs, ref value, .. } => {
                let (encoded_lhs, _, _) = self.mir_encoder.encode_place(lhs);
                stmts.extend(
                    self.encode_assign_operand(&encoded_lhs, value, location)
                );
                let target_cfg_block = cfg_blocks.get(&target).unwrap();
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

                        // Example of args[0]: 'const "internal error: entered unreachable code"'
                        let panic_message = format!("{:?}", args[0]);

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

                        if self.check_panics {
                            stmts.push(vir::Stmt::comment(format!("Rust panic - {}", panic_message)));
                            stmts.push(vir::Stmt::Assert(false.into(), pos));
                        } else {
                            debug!("Absence of panic will not be checked")
                        }
                    }

                    "<std::boxed::Box<T>>::new" => {
                        // This is the initialization of a box
                        // args[0]: value to put in the box
                        assert!(args.len() == 1);

                        let &(ref target_place, _) = destination.as_ref().unwrap();
                        let (dst, dest_ty, _) = self.mir_encoder.encode_place(target_place);
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
                            self.encode_assign_operand(&box_content, &args[0], location)
                        );
                    }

                    _ => {
                        let is_pure_function = self.encoder.env().has_attribute_name(def_id, "pure");
                        if is_pure_function {
                            let function_name = self.encoder.encode_pure_function_use(def_id);
                            debug!("Encoding pure function call '{}'", function_name);
                            assert!(destination.is_some());

                            let mut arg_exprs = Vec::new();
                            for operand in args.iter() {
                                let arg_expr = self.mir_encoder.encode_operand_expr(operand);
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

                            let pos = self.encoder.error_manager().register(
                                term.source_info.span,
                                ErrorCtxt::PureFunctionCall
                            );
                            let func_call = vir::Expr::func_app(
                                function_name,
                                arg_exprs,
                                formal_args,
                                return_type,
                                pos
                            );

                            // Havoc the lhs
                            let (target_place, target_ty, _) = match destination.as_ref() {
                                Some((ref dst, _)) => self.mir_encoder.encode_place(dst),
                                None => unreachable!()
                            };
                            stmts.extend(
                                self.encode_havoc_and_allocation(&target_place, target_ty)
                            );

                            // Initialize the lhs
                            let target_value = match destination.as_ref() {
                                Some((ref dst, _)) => self.mir_encoder.eval_place(dst),
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

                            /*
                            // Hack to work around the missing loan for arguments moved to the function call
                            for operand in args.iter() {
                                if let Some(place) = self.mir_encoder.encode_operand_place(operand) {
                                    debug!("Put permission {:?} in postcondition", place);
                                    // Choose the label that corresponds to the creation of the loan
                                    let (loans, _) = self.polonius_info.get_all_active_loans(location);
                                    let source_loans: Vec<_> = loans.iter().filter(|loan| {
                                        let loan_places = self.polonius_info.get_loan_places(loan).unwrap();
                                        let (expiring, _, restored) = self.encode_loan_places(&loan_places);
                                        trace!("Try {:?} == {:?} | {:?}", expiring, place, restored);
                                        expiring.parent() == Some(&place)
                                    }).collect();
                                    if !source_loans.is_empty() {
                                        assert_eq!(source_loans.len(), 1, "The argument depends on a condition");
                                        let source_loan = &source_loans[0];
                                        let loan_loc = self.polonius_info.get_loan_location(&source_loan);
                                        let loan_label = &self.label_after_location[&loan_loc];
                                        stmts.push(vir::Stmt::ExpireBorrow(
                                            vir::LabelledPlace::curr(place.clone()),
                                            vir::LabelledPlace::old(place.clone(), loan_label.to_string())
                                        ));
                                    }
                                }
                            }
                            */

                        } else {
                            debug!("Encoding non-pure function call '{}'", func_proc_name);
                            let mut stmts_after: Vec<vir::Stmt> = vec![];
                            let mut args_exprs: HashMap<vir::Place, vir::Expr> = HashMap::new();
                            let mut fake_arg_vars = Vec::new();

                            for operand in args.iter() {
                                let arg_ty = self.mir_encoder.get_operand_ty(operand);
                                let fake_arg = self.locals.get_fresh(arg_ty);
                                fake_arg_vars.push(fake_arg.clone());
                                let encoded_local = self.encode_prusti_local(fake_arg);
                                let fake_arg_place = vir::Place::Base(encoded_local);
                                match self.mir_encoder.encode_operand_place(operand) {
                                    Some(place) => {
                                        args_exprs.insert(fake_arg_place, place.into());
                                    }
                                    None => {
                                        let arg_val_expr = self.mir_encoder.encode_operand_expr(operand);
                                        let val_field = self.encoder.encode_value_field(arg_ty);
                                        args_exprs.insert(fake_arg_place.access(val_field), arg_val_expr);
                                    }
                                }
                            }

                            let replace_fake_args = |mut expr: vir::Expr| -> vir::Expr {
                                for (fake_arg, arg_expr) in args_exprs.iter() {
                                    expr = expr.substitute_place_with_expr(&fake_arg, arg_expr.clone());
                                }
                                expr
                            };

                            let mut encoded_target: vir::LocalVar;
                            let target = {
                                match destination.as_ref() {
                                    Some((ref target_place, _)) => {
                                        let (dst, ty, _) = self.mir_encoder.encode_place(target_place);
                                        let local = self.locals.get_fresh(ty);
                                        encoded_target = self.encode_prusti_local(local);
                                        stmts_after.push(vir::Stmt::Assign(dst, encoded_target.clone().into(), vir::AssignKind::Move));
                                        local
                                    }
                                    None => {
                                        // The return type is Never
                                        // This means that the function call never returns
                                        // So, we `assume false` after the function call
                                        stmts_after.push(vir::Stmt::Inhale(false.into()));
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
                                .get_procedure_contract_for_call(def_id, &fake_arg_vars, target);

                            let label = self.cfg_method.get_fresh_label_name();
                            assert_eq!(stmts.len(), 0);
                            if location.statement_index > 0 {
                                let prev_loc = mir::Location {
                                    statement_index: location.statement_index - 1,
                                    ..location.clone()
                                };
                                debug!("Previous loc {:?} has label {}", prev_loc, label);
                                self.label_after_location.insert(prev_loc, label.clone());
                            }
                            stmts.push(vir::Stmt::Label(label.clone()));

                            let (pre_type_spec, pre_func_spec) = self.encode_precondition_expr(&procedure_contract);
                            let pos = self.encoder.error_manager().register(
                                term.source_info.span,
                                ErrorCtxt::ExhaleMethodPrecondition
                            );
                            stmts.push(vir::Stmt::Assert(replace_fake_args(pre_func_spec), pos.clone()));
                            stmts.push(vir::Stmt::Exhale(replace_fake_args(pre_type_spec), pos));

                            let is_trusted = self.encoder.env()
                                .has_attribute_name(def_id, "trusted");

                            if is_trusted {
                                debug!("Encoding a trusted method call: {}", func_proc_name);
                                stmts.extend(
                                    self.encode_havoc(&encoded_target.into(), self.locals.get_type(target))
                                );
                            } else {
                                stmts.push(vir::Stmt::MethodCall(
                                    self.encoder.encode_procedure_use(def_id),
                                    vec![],
                                    vec![ encoded_target ],
                                ));
                            }

                            let (post_type_spec, post_func_spec) = self.encode_postcondition_expr(&procedure_contract, &label);
                            stmts.push(vir::Stmt::Inhale(replace_fake_args(post_type_spec)));
                            stmts.push(vir::Stmt::Inhale(replace_fake_args(post_func_spec)));

                            stmts.extend(stmts_after);
                        }
                    }
                    // generic (pure on non-pure) function call
                }

                if let &Some((_, target)) = destination {
                    let target_cfg_block = cfg_blocks.get(&target).unwrap();
                    (stmts, Successor::Goto(*target_cfg_block))
                } else {
                    // Encode unreachability
                    //stmts.push(
                    //    vir::Stmt::Inhale(false.into())
                    //);
                    (stmts, Successor::Return)
                }
            }

            TerminatorKind::Call { .. } => {
                // Other kind of calls?
                unimplemented!();
            }

            TerminatorKind::Assert { ref cond, expected, ref target, ref msg, .. } => {
                trace!("Assert cond '{:?}', expected '{:?}'", cond, expected);

                // Use local variables in the switch/if (see issue #57)
                let cond_var = self.cfg_method.add_fresh_local_var(vir::Type::Bool);
                stmts.push(
                    vir::Stmt::Assign(
                        cond_var.clone().into(),
                        self.mir_encoder.encode_operand_expr(cond),
                        vir::AssignKind::Copy
                    )
                );

                let viper_guard = if expected {
                    cond_var.into()
                } else {
                    vir::Expr::not(cond_var.into())
                };
                let target_cfg_block = *cfg_blocks.get(&target).unwrap();

                if self.check_panics {
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
                } else {
                    (stmts, Successor::Goto(target_cfg_block))
                }
            }

            TerminatorKind::Resume |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
        }
    }

    /// Encode permissions that are implicitly carried by the given local variable.
    fn encode_local_variable_permission(&self, local: Local) -> vir::Expr {
        self.mir_encoder.encode_place_predicate_permission(
            self.encode_prusti_local(local).into(),
            vir::Frac::one()
        ).unwrap()
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
        for item in contract.functional_precondition() {
            func_spec.push(self.encoder.encode_assertion(&item.assertion, &self.mir, &"", &encoded_args, None, false, None));
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
            predicate_name,
            vec![
                if let Some(label) = state_label {
                    self.mir_encoder.encode_old_place(encoded_place, label)
                } else {
                    encoded_place.into()
                }
            ],
            vir::Frac::one(),
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
            func_spec.push(self.encoder.encode_assertion(&item.assertion, &self.mir, label, &encoded_args, Some(&encoded_return), false, None));
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
            ErrorCtxt::ExhaleMethodPostcondition
        );
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::Assert(func_spec, pos.clone()));

        // Require the deref of reference arguments to be folded (see issue #47)
        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::comment(format!("Fold predicates for &mut args")));
        for arg_index in self.mir.args_iter() {
            let arg_ty = self.mir.local_decls[arg_index].ty;
            if self.mir_encoder.is_reference(arg_ty) {
                let encoded_arg = self.mir_encoder.encode_local(arg_index);
                let (deref_place, ..) = self.mir_encoder.encode_deref(encoded_arg.into(), arg_ty);
                let deref_pred = self.mir_encoder.encode_place_predicate_permission(deref_place, vir::Frac::one()).unwrap();
                self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::WeakObtain(deref_pred));
            }
        }

        self.cfg_method.add_stmt(return_cfg_block, vir::Stmt::Exhale(type_spec, pos));
    }

    fn encode_loop_invariant_permissions(&self, loop_head: BasicBlockIndex) -> Vec<vir::Expr> {
        let permissions_forest = self.loop_encoder.compute_loop_invariant(loop_head);
        let loop_depth = self.loop_encoder.get_loop_depth(loop_head) as u32;
        debug!("permissions_forest: {:?}", permissions_forest);

        fn read_frac_by_loop_depth(loop_depth: u32) -> vir::Frac {
            vir::Frac::new(1, 2) + vir::Frac::new(1, 2 * (1 + loop_depth))
        }

        let mut permissions = vec![];
        for tree in permissions_forest.get_trees().iter() {
            for node in tree.get_nodes().iter() {
                let kind = node.get_permission_kind();
                if kind.is_none() {
                    continue;
                }
                let mir_place = node.get_place();
                let (encoded_place, ty, _) = self.mir_encoder.encode_place(mir_place);
                if let ty::TypeVariants::TyClosure(..) = ty.sty {
                    // Do not encode closures
                    continue;
                }
                let perm = match kind {
                    /// Gives read permission to this node. It must not be a leaf node.
                    PermissionKind::ReadNode => {
                        vir::Expr::acc_permission(
                            encoded_place,
                            read_frac_by_loop_depth(loop_depth)
                        )
                    }

                    /// Gives read permission to the entire subtree including this node.
                    /// This must be a leaf node.
                    PermissionKind::ReadSubtree => {
                        vir::Expr::pred_permission(
                            vir::LabelledPlace::curr(encoded_place),
                            read_frac_by_loop_depth(loop_depth)
                        ).unwrap()
                    }

                    /// Gives write permission to this node. It must not be a leaf node.
                    PermissionKind::WriteNode => {
                        vir::Expr::acc_permission(
                            encoded_place,
                            vir::Frac::one()
                        )
                    }

                    /// Gives read permission to the entire subtree including this node.
                    /// This must be a leaf node.
                    PermissionKind::WriteSubtree => {
                        vir::Expr::pred_permission(
                            vir::LabelledPlace::curr(encoded_place),
                            vir::Frac::one()
                        ).unwrap()
                    }

                    /// Give no permission to this node and the entire subtree. This
                    /// must be a leaf node.
                    PermissionKind::None => {
                        unreachable!()
                    }
                };
                permissions.push(perm)
            }
        }

        permissions
    }

    /// Get the basic blocks that encode the specification of a loop invariant
    fn get_loop_spec_blocks(&self, loop_head: BasicBlockIndex) -> Vec<BasicBlockIndex> {
        let mut res = vec![];
        for bbi in self.procedure.get_reachable_cfg_blocks() {
            if Some(loop_head) == self.loop_encoder.get_loop_head(bbi) && self.procedure.is_spec_block(bbi) {
                res.push(bbi)
            } else {
                debug!("bbi {:?} has head {:?} and 'is spec' is {}", bbi, self.loop_encoder.get_loop_head(bbi), self.procedure.is_spec_block(bbi));
            }
        }
        res
    }

    /// Encode the functional specification of a loop
    fn encode_loop_invariant_specs(&self, loop_head: BasicBlockIndex) -> Vec<vir::Expr> {
        let spec_blocks = self.get_loop_spec_blocks(loop_head);
        trace!("loop head {:?} has spec blocks {:?}", loop_head, spec_blocks);

        let mut spec_ids = vec![];
        for bbi in spec_blocks {
            for stmt in &self.mir.basic_blocks()[bbi].statements {
                if let mir::StatementKind::Assign(
                    _,
                    mir::Rvalue::Aggregate(
                        box mir::AggregateKind::Closure(cl_def_id, _),
                        _
                    )
                ) = stmt.kind {
                    debug!("cl_def_id: {:?}", cl_def_id);
                    if let Some(attr) = self.encoder.env().get_attr(cl_def_id, "__PRUSTI_LOOP_SPEC_ID") {
                        let spec_id: u64 = attr.parse().unwrap();
                        spec_ids.push(SpecID::from(spec_id));
                    }
                }
            }
        }
        trace!("spec_ids: {:?}", spec_ids);
        assert!(spec_ids.len() <= 1, "a loop has multiple specification ids");


        let mut encoded_specs = vec![];
        if !spec_ids.is_empty() {
            let encoded_args: Vec<vir::Expr> = self.mir.args_iter()
                .map(|local| self.mir_encoder.encode_local(local).into())
                .collect();
            for spec_id in &spec_ids {
                let spec_set = self.encoder.spec().get(spec_id).unwrap();
                match spec_set {
                    SpecificationSet::Loop(ref specs) => {
                        for spec in specs.iter() {
                            // TODO: Mmm... are these parameters correct?
                            let encoded_spec = self.encoder.encode_assertion(
                                &spec.assertion,
                                self.mir,
                                PRECONDITION_LABEL,
                                &encoded_args,
                                None,
                                false,
                                Some(loop_head)
                            );
                            encoded_specs.push(encoded_spec)
                        }
                    }
                    ref x => unreachable!("{:?}", x),
                }
            }
            trace!("encoded_specs: {:?}", encoded_specs);
        }

        encoded_specs
    }

    fn encode_loop_invariant_obtain(&self, loop_head: BasicBlockIndex) -> Vec<vir::Stmt> {
        let permissions = self.encode_loop_invariant_permissions(loop_head);

        vec![
            vir::Stmt::comment(
                format!("Restore the fold/unfold state of the loop invariant of {:?}", loop_head)
            ),
            vir::Stmt::Obtain(
                permissions.into_iter().conjoin()
            )
        ]
    }

    fn encode_loop_invariant_exhale(&self, loop_head: BasicBlockIndex, after_loop_iteration: bool) -> Vec<vir::Stmt> {
        let permissions = self.encode_loop_invariant_permissions(loop_head);
        let func_spec = self.encode_loop_invariant_specs(loop_head);

        // TODO: use different positions, and generate different error messages, for the exhale
        // before the loop and after the loop body

        let assert_pos = self.encoder.error_manager().register(
            // TODO: choose a proper error span
            self.mir.span,
            if after_loop_iteration {
                ErrorCtxt::AssertLoopInvariantAfterIteration
            } else {
                ErrorCtxt::AssertLoopInvariantOnEntry
            }
        );

        let exhale_pos = self.encoder.error_manager().register(
            // TODO: choose a proper error span
            self.mir.span,
            if after_loop_iteration {
                ErrorCtxt::ExhaleLoopInvariantAfterIteration
            } else {
                ErrorCtxt::ExhaleLoopInvariantOnEntry
            }
        );

        vec![
            vir::Stmt::comment(
                format!("Assert and exhale the loop invariant of block {:?}", loop_head)
            ),
            vir::Stmt::Assert(
                func_spec.into_iter().conjoin(),
                assert_pos
            ),
            vir::Stmt::Exhale(
                permissions.into_iter().conjoin(),
                exhale_pos
            )
        ]
    }

    fn encode_loop_invariant_inhale(&self, loop_head: BasicBlockIndex) -> Vec<vir::Stmt> {
        let permissions = self.encode_loop_invariant_permissions(loop_head);
        let func_spec = self.encode_loop_invariant_specs(loop_head);

        vec![
            vir::Stmt::comment(
                format!("Inhale the loop invariant of block {:?}", loop_head)
            ),
            vir::Stmt::Inhale(
                permissions.into_iter().conjoin()
            ),
            vir::Stmt::Inhale(
                func_spec.into_iter().conjoin(),
            ),
        ]
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
    #[deprecated(note="please use `mir_encoder::encode_projection` instead")]
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
                        self.mir_encoder.encode_local(local).into(),
                        self.mir_encoder.get_local_ty(local),
                        None
                    ),
                },
            &mir::Place::Projection(ref place_projection) =>
                self.encode_projection(place_projection, root),
            x => unimplemented!("{:?}", x),
        }
    }

    /// Return type:
    /// - `Vec<vir::Stmt>`: the statements that encode the assignment of `operand` to `lhs`
    fn encode_assign_operand(&mut self, lhs: &vir::Place, operand: &mir::Operand<'tcx>, location: mir::Location) -> Vec<vir::Stmt> {
        debug!("Encode assign operand {:?}", operand);
        match operand {
            &mir::Operand::Move(ref rhs_place) => {
                let (encoded_rhs, ty, _) = self.mir_encoder.encode_place(rhs_place);
                // Move the values from `encoded_rhs` to `lhs`
                let mut stmts = vec![
                    vir::Stmt::Assign(lhs.clone(), encoded_rhs.clone().into(), vir::AssignKind::Move)
                ];
                // Store a label for this state
                let label = self.cfg_method.get_fresh_label_name();
                debug!("Current loc {:?} has label {}", location, label);
                self.label_after_location.insert(location, label.clone());
                stmts.push(vir::Stmt::Label(label.clone()));
                /*
                // Require the deref of reference arguments to be folded (see issue #47)
                if let mir::Place::Projection(box mir::Projection {
                    base: mir::Place::Local(local),
                    elem: mir::ProjectionElem::Deref
                }) = rhs_place {
                    if let mir::LocalKind::Arg = self.mir.local_kind(*local) {
                        let rhs_pred = self.mir_encoder.encode_place_predicate_permission(
                            encoded_rhs.clone(),
                            vir::Frac::new(1, 1000)
                        ).unwrap();
                        stmts.push(vir::Stmt::Obtain(rhs_pred));
                    }
                }
                // Require the deref of reference arguments to be folded (see issue #47)
                if let mir::Place::Local(local) = rhs_place {
                    if let mir::LocalKind::Arg = self.mir.local_kind(*local) {
                        if self.mir_encoder.is_reference(ty) {
                            let (deref_place, ..) = self.mir_encoder.encode_deref(
                                encoded_rhs.clone(),
                                ty
                            );
                            let deref_pred = self.mir_encoder.encode_place_predicate_permission(
                                deref_place,
                                vir::Frac::new(1, 1000)
                            ).unwrap();
                            stmts.push(vir::Stmt::Obtain(deref_pred));
                        }
                    }
                }
                */
                // Re-allocate the rhs, if it's not an argument
                let havoc_rhs = if let mir::Place::Local(rhs_local) = rhs_place {
                    if let mir::LocalKind::Arg = self.mir.local_kind(*rhs_local) {
                        false
                    } else {
                        true
                    }
                } else {
                    true
                };
                if havoc_rhs {
                    stmts.extend(
                        self.encode_havoc_and_allocation(&encoded_rhs, ty)
                    );
                } else {
                    debug!("Do not havoc rhs of '{:?}'", operand);
                }
                stmts
            }

            &mir::Operand::Copy(ref place) => {
                let (src, ty, _) = self.mir_encoder.encode_place(place);
                // Copy the values from `src` to `lhs`
                self.encode_copy(src, lhs.clone(), ty, false, location)
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
                self.mir_encoder.encode_place_predicate_permission(dst.clone(), vir::Frac::one()).unwrap()
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
    fn encode_copy(&mut self, src: vir::Place, dst: vir::Place, self_ty: ty::Ty<'tcx>, is_move: bool, location: mir::Location) -> Vec<vir::Stmt> {
        debug!("Encode copy {:?}, {:?}, {:?}", src, dst, self_ty);

        match self_ty.sty {
            ty::TypeVariants::TyBool |
            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) |
            ty::TypeVariants::TyChar => {
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
                            is_move,
                            location
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
                                is_move,
                                location
                            )
                        )
                    }
                }
                stmts
            }

            ty::TypeVariants::TyRawPtr(ty::TypeAndMut { ty, .. }) |
            ty::TypeVariants::TyRef(_, ty, _) => {
                // Ensure that we are encoding a move, not a copy (enforced byt the Rust typesystem)
                // Hack: we encode *copy* of shared references as a *move*
                //assert!(is_move);
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

    fn encode_assign_aggregate(
        &mut self,
        dst: &vir::Place,
        ty: ty::Ty<'tcx>,
        aggregate: &mir::AggregateKind<'tcx>,
        operands: &Vec<mir::Operand<'tcx>>,
        location: mir::Location
    ) -> Vec<vir::Stmt> {
        debug!("Encode aggregate {:?}, {:?}", aggregate, operands);
        let mut stmts: Vec<vir::Stmt> = vec![];
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
                        self.encode_assign_operand(&dst.clone().access(encoded_field), operand, location)
                    );
                }
                stmts
            }

            &mir::AggregateKind::Adt(adt_def, variant_index, subst, _) => {
                let num_variants = adt_def.variants.len();
                if num_variants > 1 {
                    let tcx = self.encoder.env().tcx();
                    let discr_field = self.encoder.encode_discriminant_field();
                    let discr_value = adt_def.discriminant_for_variant(tcx, variant_index).val;
                    stmts.push(
                        vir::Stmt::Assign(
                            dst.clone().access(discr_field).into(),
                            discr_value.into(),
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
                        self.encode_assign_operand(&dst.clone().access(encoded_field), operand, location)
                    );
                }
                stmts
            }

            ref x => unimplemented!("{:?}", x)
        }
    }
}
