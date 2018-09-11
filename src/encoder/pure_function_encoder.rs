// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::foldunfold;
use encoder::mir_interpreter::{ForwardMirInterpreter, run_forward_interpretation};
use encoder::mir_interpreter::{BackwardMirInterpreter, run_backward_interpretation};
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
use std::fmt;

pub struct PureFunctionEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: DefId,
    mir: &'p mir::Mir<'tcx>,
    interpreter: PureFunctionBackwardInterpreter<'p, 'v, 'r, 'a, 'tcx>
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, proc_def_id: DefId, mir: &'p mir::Mir<'tcx>) -> Self {
        trace!("PureFunctionEncoder constructor: {:?}", proc_def_id);
        PureFunctionEncoder {
            encoder,
            proc_def_id,
            mir,
            interpreter: PureFunctionBackwardInterpreter::new(encoder, mir, proc_def_id)
        }
    }

    /// Used to encode expressions in assertions
    pub fn encode_body(&self) -> vir::Expr {
        let function_name = self.encoder.env().get_item_name(self.proc_def_id);
        debug!("Encode body of pure function {}", function_name);

        let state = run_backward_interpretation(self.mir, &self.interpreter)
            .expect(&format!("Procedure {:?} contains a loop", self.proc_def_id));
        let body_expr = state.into_expression();
        debug!("Pure function {} has been encoded with expr: {}", function_name, body_expr);
        body_expr
    }

    pub fn encode_function(&self) -> vir::Function {
        let function_name = self.encode_function_name();
        info!("Encode pure function {}", function_name);

        let mut state = run_backward_interpretation(self.mir, &self.interpreter)
            .expect(&format!("Procedure {:?} contains a loop", self.proc_def_id));

        // Fix arguments
        for arg in self.mir.args_iter() {
            let arg_ty = self.interpreter.mir_encoder().get_local_ty(arg);
            let value_field = self.encoder.encode_value_field(arg_ty);
            let target_place: vir::Place = vir::Place::Base(
                self.interpreter.mir_encoder()
                    .encode_local(arg)
            ).access(value_field);
            let new_place: vir::Place = self.encode_local(arg).into();
            state.substitute_place(&target_place, new_place);
        }

        let body_expr = state.into_expression();
        debug!("Pure function {} has been encoded with expr: {}", function_name, body_expr);

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
            body: Some(body_expr)
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
        let encoded_args: Vec<vir::Expr> = contract.args.iter()
            .map(|local| self.encode_local(local.clone().into()).into())
            .collect();
        let encoded_return: vir::Expr = self.encode_local(contract.returned_value.clone().into()).into();
        for item in contract.functional_precondition() {
            func_spec.push(self.encoder.encode_assertion(&item.assertion, &self.mir, &"", &encoded_args, &encoded_return));
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
            expr = expr.substitute_place_with_expr(stored_place, stored_expr.clone());
        }
        expr
    }

    fn assign(&mut self, place: vir::Place, mut expr: vir::Expr) {
        trace!("PathState::assign {} = {}", place, expr);
        self.store.insert(place, self.translate_expr(expr));
    }

    /// Use with caution
    fn substitute_place(&mut self, place: &vir::Place, subst_place: vir::Place) {
        trace!("substitute_place {} --> {}", place, subst_place);
        self.path_cond = self.path_cond.clone().substitute_place_with_place(place, subst_place.clone());
        for (stored_place, stored_expr) in &mut self.store {
            *stored_expr = stored_expr.clone().substitute_place_with_place(place, subst_place.clone());
        }
    }

    fn add_path_condition(&mut self, mut cond: vir::Expr) {
        trace!("PathState::add_condition {}", cond);
        self.path_cond = vir::Expr::and(self.path_cond.clone(), self.translate_expr(cond));
    }

    #[deprecated(note="This method is WRONG!")]
    fn join(&self, other: &Self) -> Self {
        trace!("PathState::join {}, {}", self, other);
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

        let merged = PathState {
            path_cond: vir::Expr::or(self.path_cond.clone(), other.path_cond.clone()),
            store: merged_store
        };
        trace!("Joined state: {}", merged);
        merged
    }
}


#[derive(Clone)]
struct ForwardInterpreterState {
    states: Vec<PathState>
}

impl ForwardInterpreterState {
    fn new() -> Self {
        ForwardInterpreterState {
            states: vec![
                PathState::new()
            ]
        }
    }

    fn new_empty() -> Self {
        ForwardInterpreterState {
            states: vec![]
        }
    }

    /// Use with caution
    fn substitute_place(&mut self, place: &vir::Place, subst_place: vir::Place) {
        trace!("ForwardInterpreterState::substitute_place {} --> {}", place, subst_place);
        for mut state in self.states.iter_mut() {
            state.substitute_place(place, subst_place.clone())
        }
    }

    fn assign(&mut self, place: vir::Place, mut expr: vir::Expr) {
        trace!("ForwardInterpreterState::assign {} = {}", place, expr);
        for mut state in self.states.iter_mut() {
            state.assign(place.clone(), expr.clone())
        }
    }

    fn add_path_condition(&mut self, cond: vir::Expr) {
        trace!("ForwardInterpreterState::add_condition {}", cond);
        for mut state in self.states.iter_mut() {
            state.add_path_condition(cond.clone());
        }
    }

    fn translate(&self, place: vir::Place) -> vir::Expr {
        trace!("ForwardInterpreterState::translate {}", place);
        let guarded_exprs: Vec<_> = self.states.iter().map(
            |state| (state.path_cond.clone(), state.translate(place.clone()))
        ).collect();
        guarded_exprs.iter().skip(1).fold(
            guarded_exprs[0].1.clone(),
            |result, (guard, expr)| vir::Expr::ite(guard.clone(), expr.clone(), result)
        )
    }

    fn join(&self, other: &Self) -> Self {
        let mut states = self.states.clone();
        states.extend(other.states.clone());
        ForwardInterpreterState {
            states
        }
    }
}


impl fmt::Display for PathState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PathState {} => {{ ", self.path_cond)?;
        for (place, expr) in &self.store {
            write!(f, "{} = {}, ", place, expr)?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for ForwardInterpreterState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ForwardInterpreterState {{..{}}}", self.states.len())
    }
}

impl fmt::Debug for ForwardInterpreterState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ForwardInterpreterState ({}) {{ ", self.states.len())?;
        for state in &self.states {
            write!(f, "{}; ", state)?;
        }
        write!(f, "}}")
    }
}


#[deprecated(note="please use `PureFunctionBackwardInterpreter` instead")]
struct PureFunctionForwardInterpreter<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    mir_encoder: MirEncoder<'p, 'v, 'r, 'a, 'tcx>
}

/// XXX: This encoding works backward, but there is the risk of generating expressions whose length
/// is exponential in the number of branches.
impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionForwardInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, mir: &'p mir::Mir<'tcx>, def_id: DefId) -> Self {
        PureFunctionForwardInterpreter {
            encoder,
            mir,
            mir_encoder: MirEncoder::new_with_namespace(encoder, mir, def_id, "_pure".to_string())
        }
    }

    fn mir_encoder(&self) -> &MirEncoder<'p, 'v, 'r, 'a, 'tcx> {
        &self.mir_encoder
    }
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> ForwardMirInterpreter<'tcx> for PureFunctionForwardInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    type State = ForwardInterpreterState;

    fn initial_state(&self) -> Self::State {
        ForwardInterpreterState::new()
    }

    fn join(&self, states: &[&Self::State]) -> Self::State {
        trace!("PureFunctionForwardInterpreter::join(..{})", states.len());
        if states.len() == 0 {
            ForwardInterpreterState::new_empty()
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
        trace!("apply_statement {:?}, state: {}", stmt, state);

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

                            ty::TypeVariants::TyInt(_) |
                            ty::TypeVariants::TyUint(_) => {
                                let value_field = self.encoder.encode_value_field(src_ty);
                                let discr_value: vir::Expr = encoded_src.access(value_field).into();
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
        trace!("apply_terminator {:?}, states: {}", term, state);
        use rustc::mir::TerminatorKind;
        let mut out_states: HashMap<mir::BasicBlock, Self::State> = HashMap::new();
        let mut final_state: Option<Self::State>;

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
                            let encoded_rhs = self.mir_encoder.encode_old_expr(
                                encoded_args[0].clone(),
                                PRECONDITION_LABEL
                            );

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



#[derive(Clone, Debug)]
struct BackwardInterpreterState {
    expr: vir::Expr
}

impl BackwardInterpreterState {
    fn new(expr: vir::Expr) -> Self {
        BackwardInterpreterState {
            expr
        }
    }

    fn expr(&self) -> &vir::Expr {
        &self.expr
    }

    fn into_expression(self) -> vir::Expr {
        self.expr
    }

    pub fn substitute_place(&mut self, sub_target: &vir::Place, replacement: vir::Place) {
        trace!("substitute_place {:?} --> {:?}", sub_target, replacement);

        // If `replacement` is a reference, simplify also its dereferentiations
        if let vir::Place::AddrOf(box ref base_replacement, ref dereferenced_type) = replacement {
            trace!("Substitution of a reference. Simplify its dereferentiations.");
            let deref_field = vir::Field::new("val_ref", base_replacement.get_type().clone());
            let deref_target = sub_target.clone().access(deref_field.clone());
            self.substitute_place(&deref_target, base_replacement.clone());
        }

        self.expr = vir::utils::ExprSubPlaceSubstitutor::substitute(self.expr.clone(), sub_target, replacement);
    }

    pub fn substitute_value(&mut self, exact_target: &vir::Place, replacement: vir::Expr) {
        trace!("substitute_value {:?} --> {:?}", exact_target, replacement);
        self.expr = vir::utils::ExprExactPlaceSubstitutor::substitute(self.expr.clone(), exact_target, replacement);
    }

    pub fn uses_place(&self, sub_target: &vir::Place) -> bool {
        trace!("uses_place {:?}", sub_target);
        vir::utils::ExprPlaceFinder::find(&self.expr, sub_target)
    }
}


struct PureFunctionBackwardInterpreter<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    mir_encoder: MirEncoder<'p, 'v, 'r, 'a, 'tcx>
}

/// XXX: This encoding works backward, but there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionBackwardInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, mir: &'p mir::Mir<'tcx>, def_id: DefId) -> Self {
        PureFunctionBackwardInterpreter {
            encoder,
            mir,
            mir_encoder: MirEncoder::new_with_namespace(encoder, mir, def_id, "_pure".to_string()),
        }
    }

    fn mir_encoder(&self) -> &MirEncoder<'p, 'v, 'r, 'a, 'tcx> {
        &self.mir_encoder
    }
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> BackwardMirInterpreter<'tcx> for PureFunctionBackwardInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    type State = BackwardInterpreterState;

    fn apply_terminator(&self, term: &mir::Terminator<'tcx>, states: HashMap<mir::BasicBlock, &Self::State>) -> Self::State {
        trace!("apply_terminator {:?}, states: {:?}", term, states);
        use rustc::mir::TerminatorKind;

        // Generate a function call that leaves the expression undefined.
        // TODO: generate unique names for each use
        let undef_expr = {
            let uuid = format!(
                "defid_{}_{}$undef_expr",
                self.mir_encoder.def_id().krate,
                self.mir_encoder.def_id().index.as_raw_u32()
            );
            let encoded_type = self.encoder.encode_value_type(self.mir.return_ty());
            let function_name = self.encoder.encode_builtin_function_use(
                BuiltinFunctionKind::Undefined(uuid, encoded_type.clone())
            );
            vir::Expr::FuncApp(function_name, vec![], vec![], encoded_type)
        };

        match term.kind {
            TerminatorKind::Unreachable |
            TerminatorKind::Abort |
            TerminatorKind::Drop{..} |
            TerminatorKind::Resume{..} => {
                assert!(states.is_empty());
                BackwardInterpreterState::new(undef_expr)
            }

            TerminatorKind::Goto { ref target } => {
                assert_eq!(states.len(), 1);
                states[target].clone()
            }

            TerminatorKind::FalseEdges { ref real_target, .. } => {
                assert_eq!(states.len(), 2);
                states[real_target].clone()
            }

            TerminatorKind::FalseUnwind { ref real_target, .. } => {
                assert_eq!(states.len(), 1);
                states[real_target].clone()
            }

            TerminatorKind::Return => {
                assert!(states.is_empty());
                trace!("Return type: {:?}", self.mir.return_ty());
                let return_type = self.encoder.encode_type(self.mir.return_ty());
                let return_var = vir::LocalVar::new("_pure_0", return_type);
                let field = self.encoder.encode_value_field(self.mir.return_ty());
                BackwardInterpreterState::new(vir::Place::Base(return_var.into()).access(field).into())
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

                BackwardInterpreterState::new(
                    cfg_targets.into_iter().fold(
                        states[&default_target].expr().clone(),
                        |else_expr, (guard, then_target)|
                            vir::Expr::ite(guard, states[&then_target].expr().clone(), else_expr)
                    )
                )
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
                    let (ref lhs_place, target_block) = destination.as_ref().unwrap();
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
                            let mut state = states[&target_block].clone();
                            state.substitute_value(&lhs_value, encoded_rhs);
                            state
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

                            let mut state = states[&target_block].clone();
                            state.substitute_value(&lhs_value, encoded_rhs);
                            state
                        }
                    }
                } else {
                    // Encoding of a non-terminating function call
                    BackwardInterpreterState::new(undef_expr)
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

                BackwardInterpreterState::new(
                    vir::Expr::ite(
                        viper_guard,
                        states[target].expr().clone(),
                        undef_expr
                    )
                )
            }

            TerminatorKind::Resume |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
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

                if !state.uses_place(&encoded_lhs) {
                    // If the lhs is not mentioned in our state, do nothing
                    trace!("The state does not mention {:?}", encoded_lhs);
                    return
                }

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
                                // Substitute a place
                                state.substitute_place(&encoded_lhs, encode_rhs);
                            },
                            None => {
                                // Substitute a place of a value with an expression
                                let rhs_expr = self.mir_encoder.encode_operand_expr(operand);
                                state.substitute_value(&opt_lhs_value_place.unwrap(), rhs_expr);
                            },
                        }
                    }

                    &mir::Rvalue::Aggregate(..) => {
                        unimplemented!()
                    }

                    &mir::Rvalue::BinaryOp(op, ref left, ref right) => {
                        let encoded_left = self.mir_encoder.encode_operand_expr(left);
                        let encoded_right = self.mir_encoder.encode_operand_expr(right);
                        let encoded_value = self.mir_encoder.encode_bin_op_expr(op, encoded_left, encoded_right, ty);

                        // Substitute a place of a value with an expression
                        state.substitute_value(&opt_lhs_value_place.unwrap(), encoded_value);
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

                        // Substitute a place of a value with an expression
                        state.substitute_value(&lhs_value, encoded_value);
                        state.substitute_value(&lhs_check, encoded_check);
                    }

                    &mir::Rvalue::UnaryOp(op, ref operand) => {
                        let encoded_val = self.mir_encoder.encode_operand_expr(operand);
                        let encoded_value = self.mir_encoder.encode_unary_op_expr(op, encoded_val);

                        // Substitute a place of a value with an expression
                        state.substitute_value(&opt_lhs_value_place.unwrap(), encoded_value);
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

                                // Substitute a place of a value with an expression
                                state.substitute_value(&opt_lhs_value_place.unwrap(), discr_value);
                            }
                            ref x => {
                                panic!("The discriminant of type {:?} is not defined", x);
                            }
                        }
                    }

                    &mir::Rvalue::Ref(_, mir::BorrowKind::Unique, ref place) |
                    &mir::Rvalue::Ref(_, mir::BorrowKind::Mut{ .. }, ref place) |
                    &mir::Rvalue::Ref(_, mir::BorrowKind::Shared, ref place) => {
                        let encoded_place = self.mir_encoder.encode_place(place).0;
                        let encoded_ref = match encoded_place {
                            vir::Place::Field(box ref base, vir::Field { ref name, .. }) if name == "val_ref" => {
                                base.clone()
                            }
                            other_place => other_place.addr_of()
                        };

                        // Substitute the place
                        state.substitute_place(&encoded_lhs, encoded_ref);
                    }

                    ref rhs => {
                        unimplemented!("encoding of '{:?}'", rhs);
                    }
                }
            }

            ref stmt => unimplemented!("encoding of '{:?}'", stmt)
        }
    }
}
