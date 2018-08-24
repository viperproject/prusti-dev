// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::foldunfold;
use encoder::mir_interpreter::{ForwardMirInterpreter, run_forward_interpretation};
use encoder::mir_encoder::MirEncoder;
use encoder::builtin_encoder::BuiltinFunctionKind;
use encoder::mir_encoder::PRECONDITION_LABEL;
use encoder::vir;
use rustc::mir;
use rustc::ty;
use rustc::hir::def_id::DefId;
use std::collections::HashMap;
use std::collections::HashSet;
use prusti_interface::environment::Environment;
use syntax::ast;
use prusti_interface::report::Log;
use encoder::borrows::ProcedureContract;
use encoder::places;
use encoder::vir::ExprIterator;

pub struct PureFunctionEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: DefId,
    mir: &'p mir::Mir<'tcx>,
    interpreter: PureFunctionInterpreter<'p, 'v, 'r, 'a, 'tcx>
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, proc_def_id: DefId, mir: &'p mir::Mir<'tcx>) -> Self {
        trace!("PureFunctionEncoder constructor: {:?}", proc_def_id);
        PureFunctionEncoder {
            encoder,
            proc_def_id,
            mir,
            interpreter: PureFunctionInterpreter::new(encoder, mir)
        }
    }

    /// Used to encode expressions in assertions
    pub fn encode_body(&self) -> vir::Expr {
        let function_name = self.encoder.env().get_item_name(self.proc_def_id);
        debug!("Encode body of pure function {}", function_name);

        let states = run_forward_interpretation(self.mir, &self.interpreter);
        let return_place = vir::Place::Base(
            self.interpreter.mir_encoder.encode_local(mir::RETURN_PLACE)
        ).access(
            self.encoder.encode_value_field(self.mir.return_ty())
        );
        let return_expr = states.join_states().translate(return_place);
        debug!("Pure function {} has been encoded with expr: {}", function_name, return_expr);
        return_expr
    }

    pub fn encode_function(&self) -> vir::Function {
        let function_name = self.encode_function_name();
        debug!("Encode pure function {}", function_name);

        let mut states = run_forward_interpretation(self.mir, &self.interpreter);
        let return_place = vir::Place::Base(
            self.interpreter.mir_encoder.encode_local(mir::RETURN_PLACE)
        ).access(
            self.encoder.encode_value_field(self.mir.return_ty())
        );
        let return_expr = states.join_states().translate(return_place);
        debug!("Pure function {} has been encoded with expr: {}", function_name, return_expr);

        let contract = self.encoder.get_procedure_contract_for_def(self.proc_def_id);
        let preconditions = self.encode_precondition_expr(&contract);

        let formal_args: Vec<_> = self.mir.args_iter().map(
            |local| self.encode_local(local)
        ).collect();
        let return_type = self.encode_function_return_type();

        let function = vir::Function {
            name: function_name.clone(),
            formal_args,
            return_type,
            pres: vec![preconditions.0, preconditions.1],
            body: Some(return_expr)
        };

        self.encoder.log_vir_initial_program(function.to_string());

        // Add folding/unfolding
        let final_function = foldunfold::add_folding_unfolding(function, self.encoder.get_used_viper_predicates_map());

        final_function
    }

    /// Encode the precondition with two expressions:
    /// - one for the type encoding
    /// - one for the functional specification.
    fn encode_precondition_expr(&self, contract: &ProcedureContract<'tcx>) -> (vir::Expr, vir::Expr) {
        let type_spec = contract.args.iter()
            .flat_map(|&local|
                self.interpreter.mir_encoder().encode_place_predicate_permission(
                    self.encode_local(local.into()).into()
                )
            );
        let mut func_spec: Vec<vir::Expr> = vec![];

        // Encode functional specification
        for item in contract.functional_precondition() {
            func_spec.push(self.encoder.encode_assertion(&item.assertion, &self.mir));
        }

        (type_spec.into_iter().conjoin(), func_spec.into_iter().conjoin())
    }

    fn encode_local(&self, local: mir::Local) -> vir::LocalVar {
        let var_name = self.interpreter.mir_encoder().encode_local_var_name(local);
        let var_type = self.encoder.encode_value_type(
            self.interpreter.mir_encoder().get_local_ty(local)
        );
        vir::LocalVar::new(var_name, var_type)
    }

    pub fn encode_function_name(&self) -> String {
        self.encoder.encode_item_name(self.proc_def_id)
    }

    pub fn encode_function_return_type(&self) -> vir::Type {
        self.encoder.encode_value_type(self.mir.return_ty())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PathState {
    path_cond: vir::Expr,
    store: HashMap<vir::Place, vir::Expr>
}

impl PathState {
    fn new() -> Self {
        PathState {
            path_cond: true.into(),
            store: HashMap::new()
        }
    }

    fn translate(&self, place: vir::Place) -> vir::Expr {
        trace!("[enter] translate {}", place);
        let expr = self.translate_expr(place.clone().into());
        trace!("[exit] translate {} => {}", place, expr);
        expr
    }

    fn translate_expr(&self, mut expr: vir::Expr) -> vir::Expr {
        trace!("translate_expr {}", expr);
        for (stored_place, stored_expr) in &self.store {
            expr = vir::utils::substitute_place_in_expr(expr, stored_place, stored_expr.clone());
        }
        expr
    }

    fn assign(&mut self, place: vir::Place, mut expr: vir::Expr) {
        trace!("PathState::assign {} = {}", place, expr);
        self.store.insert(place, self.translate_expr(expr));
    }

    fn add_path_condition(&mut self, mut cond: vir::Expr) {
        trace!("PathState::add_condition {}", cond);
        self.path_cond = vir::Expr::and(self.path_cond.clone(), self.translate_expr(cond));
    }

    fn join(&self, other: &Self) -> Self {
        let mut merged_store = self.store.clone();

        for (place, other_value) in &other.store {
            if merged_store.contains_key(&place) {
                let self_value = &merged_store[&place];
                let merged_value = if self_value == other_value {
                    self_value.clone()
                } else {
                    vir::Expr::ite(
                        self.path_cond.clone(),
                        self_value.clone(),
                        other_value.clone()
                    )
                };
                merged_store.insert(place.clone(), merged_value);
            } else {
                merged_store.insert(place.clone(), other_value.clone());
            }
        }

        PathState {
            path_cond: vir::Expr::or(self.path_cond.clone(), other.path_cond.clone()),
            store: merged_store
        }
    }
}

fn join_path_states(states: &[&PathState]) -> PathState {
    trace!("join_path_states(..{})", states.len());
    assert!(states.len() > 0);
    if states.len() == 1 {
        states[0].clone()
    } else {
        let mid = states.len() / 2;
        let left_states = &states[..mid];
        let right_states = &states[mid..];
        join_path_states(left_states).join(&join_path_states(right_states))
    }
}


#[derive(Clone, Debug)]
struct InterpreterState {
    states: Vec<PathState>
}

impl InterpreterState {
    fn new() -> Self {
        InterpreterState {
            states: vec![
                PathState::new()
            ]
        }
    }

    fn new_empty() -> Self {
        InterpreterState {
            states: vec![]
        }
    }

    fn assign(&mut self, place: vir::Place, mut expr: vir::Expr) {
        trace!("InterpreterState::assign {} = {}", place, expr);
        for mut state in self.states.iter_mut() {
            state.assign(place.clone(), expr.clone())
        }
    }

    fn add_path_condition(&mut self, cond: vir::Expr) {
        trace!("InterpreterState::add_condition {}", cond);
        for mut state in self.states.iter_mut() {
            state.add_path_condition(cond.clone());
        }
    }

    fn join_states(&self) -> PathState {
        trace!("join_states(..{})", self.states.len());
        join_path_states(&self.states.iter().collect::<Vec<_>>()[..])
    }

    fn join(&self, other: &Self) -> Self {
        let mut states = self.states.clone();
        states.extend(other.states.clone());
        InterpreterState {
            states
        }
    }
}


struct PureFunctionInterpreter<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    mir_encoder: MirEncoder<'p, 'v, 'r, 'a, 'tcx>
}

/// XXX: This encoding works backward, but there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, mir: &'p mir::Mir<'tcx>) -> Self {
        PureFunctionInterpreter {
            encoder,
            mir,
            mir_encoder: MirEncoder::new(encoder, mir)
        }
    }

    fn mir_encoder(&self) -> &MirEncoder<'p, 'v, 'r, 'a, 'tcx> {
        &self.mir_encoder
    }
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> ForwardMirInterpreter<'tcx> for PureFunctionInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    type State = InterpreterState;

    fn initial_state(&self) -> Self::State {
        InterpreterState::new()
    }

    fn join(&self, states: &[&Self::State]) -> Self::State {
        trace!("join(..{})", states.len());
        if states.len() == 0 {
            InterpreterState::new_empty()
        } else if states.len() == 1 {
            states[0].clone()
        } else {
            let mid = states.len() / 2;
            let left_states = &states[..mid];
            let right_states = &states[mid..];
            self.join(left_states).join(&self.join(right_states))
        }
    }

    fn apply_statement(&self, stmt: &mir::Statement<'tcx>, state: &mut Self::State) {
        trace!("apply_statement {:?}, state: {:?}", stmt, state);

        match stmt.kind {
            mir::StatementKind::StorageLive(..) |
            mir::StatementKind::StorageDead(..) |
            mir::StatementKind::ReadForMatch(..) |
            mir::StatementKind::EndRegion(..) => {
                // Nothing to do
            }

            mir::StatementKind::Assign(ref lhs, ref rhs) => {
                let (encoded_lhs, ty, _) = self.mir_encoder.encode_place(lhs);

                let opt_lhs_value_place = match ty.sty {
                    ty::TypeVariants::TyBool |
                    ty::TypeVariants::TyInt(..) |
                    ty::TypeVariants::TyUint(..) |
                    ty::TypeVariants::TyRawPtr(..) |
                    ty::TypeVariants::TyRef(..) => {
                        Some(encoded_lhs.clone().access(self.encoder.encode_value_field(ty)))
                    }
                    _ => None
                };

                let type_name = self.encoder.encode_type_predicate_use(ty);
                match rhs {
                    &mir::Rvalue::Use(ref operand) => {
                        let opt_encoded_rhs = self.mir_encoder.encode_operand_place(operand);

                        match opt_encoded_rhs {
                            Some(encode_rhs) => {
                                // Assign using a place
                                state.assign(encoded_lhs, encode_rhs.into());
                            },
                            None => {
                                // Assign using an expression
                                let rhs_expr = self.mir_encoder.encode_operand_expr(operand);
                                state.assign(opt_lhs_value_place.unwrap(), rhs_expr);
                            },
                        }
                    }

                    &mir::Rvalue::Aggregate(..) => {
                        unimplemented!()
                    }

                    &mir::Rvalue::BinaryOp(op, ref left, ref right) => {
                        let encoded_left = self.mir_encoder.encode_operand_expr(left);
                        let encoded_right = self.mir_encoder.encode_operand_expr(right);

                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.mir_encoder.encode_bin_op_expr(op, encoded_left, encoded_right, ty);

                        // Assign using an expression
                        state.assign(opt_lhs_value_place.unwrap(), encoded_value);
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

                        let lhs_value = encoded_lhs.clone()
                            .access(value_field)
                            .access(value_field_value);
                        let lhs_check = encoded_lhs.clone()
                            .access(check_field)
                            .access(check_field_value);

                        // Assign using an expression
                        state.assign(lhs_value, encoded_value);
                        state.assign(lhs_check, encoded_check);
                    }

                    &mir::Rvalue::UnaryOp(op, ref operand) => {
                        let encoded_val = self.mir_encoder.encode_operand_expr(operand);

                        let field = self.encoder.encode_value_field(ty);
                        let encoded_value = self.mir_encoder.encode_unary_op_expr(op, encoded_val);

                        unimplemented!()
                    }

                    &mir::Rvalue::NullaryOp(op, ref op_ty) => {
                        unimplemented!()
                    }

                    &mir::Rvalue::Discriminant(ref src) => {
                        let (encoded_src, src_ty, _) = self.mir_encoder.encode_place(src);
                        match src_ty.sty {
                            ty::TypeVariants::TyAdt(ref adt_def, _) if !adt_def.is_box() => {
                                let num_variants = adt_def.variants.len();

                                let discr_value: vir::Expr = if num_variants <= 1 {
                                    0.into()
                                } else {
                                    let discr_field = self.encoder.encode_discriminant_field();
                                    encoded_src.access(discr_field).into()
                                };

                                // Assing using an expression
                                state.assign(opt_lhs_value_place.unwrap(), discr_value);
                            }
                            ref x => {
                                panic!("The discriminant of type {:?} is not defined", x);
                            }
                        }
                    }

                    &mir::Rvalue::Ref(ref _region, mir::BorrowKind::Shared, ref place) => {
                        let encoded_place = self.mir_encoder.encode_place(place).0;
                        let encoded_ref = match encoded_place {
                            vir::Place::Field(box ref base, vir::Field { ref name, .. }) if name == "val_ref" => {
                                base.clone()
                            }
                            other_place => other_place.addr_of()
                        };

                        // Assign using a place
                        state.assign(encoded_lhs, encoded_ref.into());
                    }

                    &mir::Rvalue::Ref(ref _region, mir::BorrowKind::Unique, ref place) |
                    &mir::Rvalue::Ref(ref _region, mir::BorrowKind::Mut{ .. }, ref place)=> {
                        let ref_field = self.encoder.encode_value_field(ty);
                        let (encoded_value, _, _) = self.mir_encoder.encode_place(place);

                        unimplemented!()
                    }

                    ref rhs => {
                        unimplemented!("encoding of '{:?}'", rhs);
                    }
                }
            }

            ref stmt => unimplemented!("encoding of '{:?}'", stmt)
        }
    }

    fn apply_terminator(&self, term: &mir::Terminator<'tcx>, state: &Self::State) -> (HashMap<mir::BasicBlock, Self::State>, Option<Self::State>) {
        trace!("apply_terminator {:?}, states: {:?}", term, state);
        use rustc::mir::TerminatorKind;
        let mut out_states: HashMap<mir::BasicBlock, Self::State> = HashMap::new();
        let mut final_state: Option<Self::State>;

        let undef_expr = {
            // Generate a function call that leaves the expression undefined.
            let return_type = self.encoder.encode_value_type(self.mir.return_ty());
            let function_name = self.encoder.encode_builtin_function_use(
                BuiltinFunctionKind::Undefined(return_type.clone())
            );
            vir::Expr::FuncApp(function_name, vec![], vec![], return_type)
        };

        match term.kind {
            TerminatorKind::Unreachable |
            TerminatorKind::Abort |
            TerminatorKind::Drop{..} |
            TerminatorKind::Resume{..} => {
                // Discard state
                final_state = None;
            }

            TerminatorKind::Goto { ref target } => {
                out_states.insert(*target, state.clone());
                final_state = None;
            }

            TerminatorKind::FalseEdges { ref real_target, .. } |
            TerminatorKind::FalseUnwind { ref real_target, .. } => {
                out_states.insert(*real_target, state.clone());
                final_state = None;
            }

            TerminatorKind::Return => {
                final_state = Some(state.clone());
            }

            TerminatorKind::SwitchInt { ref targets, ref discr, ref values, switch_ty } => {
                trace!("SwitchInt ty '{:?}', discr '{:?}', values '{:?}'", switch_ty, discr, values);
                let mut cfg_targets: Vec<(vir::Expr, mir::BasicBlock)> = vec![];
                let discr_val = self.mir_encoder.encode_operand_expr(discr);
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
                    cfg_targets.push((viper_guard, target))
                }
                let default_target = targets[values.len()];

                for (viper_guard, target) in &cfg_targets {
                    let mut target_state = state.clone();
                    target_state.add_path_condition(viper_guard.clone());
                    out_states.insert(*target, target_state);
                }

                let default_guard = vir::Expr::not(
                    cfg_targets.into_iter().map(|(guard, _)| guard).disjoin()
                );
                let mut default_target_state = state.clone();
                default_target_state.add_path_condition(default_guard.clone());
                out_states.insert(default_target, default_target_state);

                final_state = None;
            }

            TerminatorKind::DropAndReplace { ref target, ref location, ref value, .. } => {
                unimplemented!();
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
                if destination.is_some() {
                    let func_proc_name: &str = &self.encoder.env().get_item_name(def_id);
                    let (ref lhs_place, target_bb) = destination.as_ref().unwrap();
                    let (encoded_lhs, ty, _) = self.mir_encoder.encode_place(lhs_place);
                    let lhs_value = encoded_lhs.clone().access(self.encoder.encode_value_field(ty));
                    let encoded_args: Vec<vir::Expr> = args.iter()
                        .map(|arg| self.mir_encoder.encode_operand_expr(arg))
                        .collect();

                    match func_proc_name {
                        "prusti_contracts::internal::old" => {
                            trace!("Encoding old expression {:?}", args[0]);
                            assert!(args.len() == 1);
                            let encoded_rhs = self.mir_encoder.encode_old_expr(encoded_args[0].clone(), PRECONDITION_LABEL);

                            let mut new_state = state.clone();
                            new_state.assign(lhs_value, encoded_rhs);
                            out_states.insert(*target_bb, new_state);
                            final_state = None;
                        }

                        // generic function call
                        _ => {
                            let function_name = self.encoder.encode_pure_function_use(def_id);
                            trace!("Encoding pure function call '{}'", function_name);

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

                            let encoded_rhs = vir::Expr::func_app(
                                function_name,
                                encoded_args,
                                formal_args,
                                return_type
                            );

                            let mut new_state = state.clone();
                            new_state.assign(lhs_value, encoded_rhs);
                            out_states.insert(*target_bb, new_state);
                            final_state = None;
                        }
                    }
                } else {
                    // Encoding of a non-terminating function call
                    final_state = None;
                }
            }

            TerminatorKind::Call { .. } => {
                // Other kind of calls?
                unimplemented!();
            }

            TerminatorKind::Assert { ref cond, expected, ref target, ref msg, .. } => {
                let cond_val = self.mir_encoder.encode_operand_expr(cond);
                let viper_guard = if expected {
                    cond_val
                } else {
                    vir::Expr::not(cond_val)
                };

                let mut new_state = state.clone();
                new_state.add_path_condition(viper_guard);
                out_states.insert(*target, new_state);
                final_state = None;
            }

            TerminatorKind::Resume |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
        };

        (out_states, final_state)
    }
}
