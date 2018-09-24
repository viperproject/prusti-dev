// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::Encoder;
use encoder::foldunfold;
use encoder::mir_interpreter::{ForwardMirInterpreter, run_forward_interpretation};
use encoder::mir_interpreter::{BackwardMirInterpreter, run_backward_interpretation, MultiExprBackwardInterpreterState};
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
use rustc_data_structures::indexed_vec::Idx;

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
            interpreter: PureFunctionBackwardInterpreter::new(encoder, mir, proc_def_id, "_pure".to_string())
        }
    }

    /// Used to encode expressions in assertions
    pub fn encode_body(&self) -> vir::Expr {
        let function_name = self.encoder.env().get_item_name(self.proc_def_id);
        debug!("Encode body of pure function {}", function_name);

        let state = run_backward_interpretation(self.mir, &self.interpreter)
            .expect(&format!("Procedure {:?} contains a loop", self.proc_def_id));
        let body_expr = state.into_expressions().remove(0);
        debug!("Pure function {} has been encoded with expr: {}", function_name, body_expr);
        body_expr
    }

    pub fn encode_function(&self) -> vir::Function {
        let function_name = self.encode_function_name();
        debug!("Encode pure function {}", function_name);

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

        let body_expr = state.into_expressions().remove(0);
        debug!("Pure function {} has been encoded with expr: {}", function_name, body_expr);

        self.encode_function_given_body(Some(body_expr))
    }

    pub fn encode_bodyless_function(&self) -> vir::Function {
        let function_name = self.encode_function_name();
        debug!("Encode trusted (bodyless) pure function {}", function_name);

        self.encode_function_given_body(None)
    }

    /// Private
    fn encode_function_given_body(&self, body: Option<vir::Expr>) -> vir::Function {
        let function_name = self.encode_function_name();
        let is_bodyless = body.is_none();
        if is_bodyless {
            debug!("Encode pure function {} given body None", function_name);
        } else {
            debug!("Encode pure function {} given body Some({})", function_name, body.as_ref().unwrap());
        }

        let contract = self.encoder.get_procedure_contract_for_def(self.proc_def_id);
        let preconditions = self.encode_precondition_expr(&contract);
        let postcondition = self.encode_postcondition_expr(&contract);

        let formal_args: Vec<_> = self.mir.args_iter().map(
            |local| self.encode_local(local)
        ).collect();
        let return_type = self.encode_function_return_type();

        let function = vir::Function {
            name: function_name.clone(),
            formal_args,
            return_type,
            pres: vec![preconditions.0, preconditions.1],
            posts: vec![postcondition],
            body
        };

        self.encoder.log_vir_program_before_foldunfold(function.to_string());

        // Add folding/unfolding
        let final_function = if is_bodyless {
            function
        } else {
            foldunfold::add_folding_unfolding(function, self.encoder.get_used_viper_predicates_map())
        };

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
        let encoded_return = self.encode_local(contract.returned_value.clone().into());
        debug!("encoded_return: {:?}", encoded_return);
        for item in contract.functional_precondition() {
            debug!("Encode spec item: {:?}", item);
            func_spec.push(self.encoder.encode_assertion(&item.assertion, &self.mir, &"", &encoded_args, &encoded_return.clone().into(), true));
        }

        (type_spec.into_iter().conjoin(), func_spec.into_iter().conjoin())
    }

    /// Encode the postcondition with one expression just for the functional specification (no
    /// type encoding).
    fn encode_postcondition_expr(&self, contract: &ProcedureContract<'tcx>) -> vir::Expr {
        let mut func_spec: Vec<vir::Expr> = vec![];

        // Encode functional specification
        let encoded_args: Vec<vir::Expr> = contract.args.iter()
            .map(|local| self.encode_local(local.clone().into()).into())
            .collect();
        let encoded_return = self.encode_local(contract.returned_value.clone().into());
        debug!("encoded_return: {:?}", encoded_return);
        for item in contract.functional_postcondition() {
            func_spec.push(self.encoder.encode_assertion(&item.assertion, &self.mir, &"", &encoded_args, &encoded_return.clone().into(), true));
        }

        let post = func_spec.into_iter().conjoin();

        // Fix return variable
        let pure_fn_return_variable = vir::LocalVar::new("__result", self.encode_function_return_type());
        post.substitute_place_with_place(&encoded_return.into(), pure_fn_return_variable.into())
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


pub(super) struct PureFunctionBackwardInterpreter<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    mir_encoder: MirEncoder<'p, 'v, 'r, 'a, 'tcx>,
    namespace: String
}

/// XXX: This encoding works backward, but there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PureFunctionBackwardInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    pub(super) fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, mir: &'p mir::Mir<'tcx>, def_id: DefId, namespace: String) -> Self {
        PureFunctionBackwardInterpreter {
            encoder,
            mir,
            mir_encoder: MirEncoder::new_with_namespace(encoder, mir, def_id, namespace.clone()),
            namespace
        }
    }

    pub(super) fn mir(&self) -> &mir::Mir<'tcx> {
        self.mir
    }

    pub(super) fn mir_encoder(&self) -> &MirEncoder<'p, 'v, 'r, 'a, 'tcx> {
        &self.mir_encoder
    }

    pub(super) fn encoder(&self) -> &Encoder<'v, 'r, 'a, 'tcx> {
        &self.encoder
    }
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> BackwardMirInterpreter<'tcx> for PureFunctionBackwardInterpreter<'p, 'v, 'r, 'a, 'tcx> {
    type State = MultiExprBackwardInterpreterState;

    fn apply_terminator(&self, bb: mir::BasicBlock, term: &mir::Terminator<'tcx>, states: HashMap<mir::BasicBlock, &Self::State>) -> Self::State {
        trace!("apply_terminator {:?}, states: {:?}", term, states);
        use rustc::mir::TerminatorKind;

        // Generate a function call that leaves the expression undefined.
        // TODO: generate unique names for each use
        let undef_expr = |id| {
            let uuid = format!(
                "undef_expr$defid_{}_{}$bb_{}$id_{}",
                self.mir_encoder.def_id().krate,
                self.mir_encoder.def_id().index.as_raw_u32(),
                bb.index(),
                id
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
                MultiExprBackwardInterpreterState::new_single(undef_expr(0))
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
                let return_var = vir::LocalVar::new(format!("{}_0", self.namespace), return_type);
                let field = self.encoder.encode_value_field(self.mir.return_ty());
                MultiExprBackwardInterpreterState::new_single(vir::Place::Base(return_var.into()).access(field).into())
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

                let default_target_terminator = self.mir.basic_blocks()[default_target].terminator.as_ref().unwrap();
                trace!("default_target_terminator: {:?}", default_target_terminator);
                let default_is_unreachable = match default_target_terminator.kind {
                    TerminatorKind::Unreachable => true,
                    _ => false
                };

                trace!("cfg_targets: {:?}", cfg_targets);

                let refined_default_target = if default_is_unreachable && !cfg_targets.is_empty() {
                    // Here we can assume that the `cfg_targets` are exhausive, and that
                    // `default_target` is unreachable
                    trace!("The default target is unreachable");
                    cfg_targets.pop().unwrap().1
                } else {
                    default_target
                };

                trace!("cfg_targets: {:?}", cfg_targets);

                MultiExprBackwardInterpreterState::new(
                    (0..states[&refined_default_target].exprs().len()).map(
                        |expr_index| {
                            cfg_targets.iter().fold(
                                states[&refined_default_target].exprs()[expr_index].clone(),
                                |else_expr, (guard, target)| {
                                    vir::Expr::ite(
                                        guard.clone(),
                                        states[&target].exprs()[expr_index].clone(),
                                        else_expr
                                    )
                                }
                            )
                        }
                    ).collect()
                )
            }

            TerminatorKind::DropAndReplace { ref target, ref location, ref value, .. } => {
                unimplemented!()
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
                    MultiExprBackwardInterpreterState::new_single(undef_expr(0))
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

                MultiExprBackwardInterpreterState::new(
                    states[target].exprs().iter().enumerate().map(
                        |(index, expr)| {
                            vir::Expr::ite(
                                viper_guard.clone(),
                                expr.clone(),
                                undef_expr(index)
                            )
                        }
                    ).collect()
                )
            }

            TerminatorKind::Resume |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
        }
    }

    fn apply_statement(&self, bb: mir::BasicBlock, stmt_index: usize, stmt: &mir::Statement<'tcx>, state: &mut Self::State) {
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

                if !state.use_place(&encoded_lhs) {
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
                            Some(encoded_rhs) => {
                                // Substitute a place
                                state.substitute_place(&encoded_lhs, encoded_rhs);
                            },
                            None => {
                                // Substitute a place of a value with an expression
                                let rhs_expr = self.mir_encoder.encode_operand_expr(operand);
                                state.substitute_value(&opt_lhs_value_place.unwrap(), rhs_expr);
                            },
                        }
                    }

                    &mir::Rvalue::Aggregate(ref aggregate, ref operands) => {
                        debug!("Encode aggregate {:?}, {:?}", aggregate, operands);
                        match aggregate.as_ref() {
                            &mir::AggregateKind::Tuple => {
                                let field_types = if let ty::TypeVariants::TyTuple(ref x) = ty.sty { x } else { unreachable!() };
                                for (field_num, operand) in operands.iter().enumerate() {
                                    let field_name = format!("tuple_{}", field_num);
                                    let field_ty = field_types[field_num];
                                    let encoded_field = self.encoder.encode_ref_field(&field_name, field_ty);
                                    let field_place = encoded_lhs.clone().access(encoded_field);

                                    match self.mir_encoder.encode_operand_place(operand) {
                                        Some(encoded_rhs) => {
                                            // Substitute a place
                                            state.substitute_place(&field_place, encoded_rhs);
                                        },
                                        None => {
                                            // Substitute a place of a value with an expression
                                            let rhs_expr = self.mir_encoder.encode_operand_expr(operand);
                                            let value_field = self.encoder.encode_value_field(field_ty);
                                            state.substitute_value(&field_place.access(value_field), rhs_expr);
                                        },
                                    }
                                }
                            }

                            &mir::AggregateKind::Adt(adt_def, variant_index, subst, _) => {
                                let num_variants = adt_def.variants.len();
                                if num_variants > 1 {
                                    let discr_field = self.encoder.encode_discriminant_field();
                                    state.substitute_value(
                                        &encoded_lhs.clone().access(discr_field),
                                        variant_index.into()
                                    );
                                }
                                let variant_def = &adt_def.variants[variant_index];
                                for (field_index, field) in variant_def.fields.iter().enumerate() {
                                    let operand = &operands[field_index];
                                    let field_name = format!("enum_{}_{}", variant_index, field.ident.as_str());
                                    let tcx = self.encoder.env().tcx();
                                    let field_ty = field.ty(tcx, subst);
                                    let encoded_field = self.encoder.encode_ref_field(&field_name, field_ty);

                                    let field_place = encoded_lhs.clone().access(encoded_field);
                                    match self.mir_encoder.encode_operand_place(operand) {
                                        Some(encoded_rhs) => {
                                            // Substitute a place
                                            state.substitute_place(&field_place, encoded_rhs);
                                        },
                                        None => {
                                            // Substitute a place of a value with an expression
                                            let rhs_expr = self.mir_encoder.encode_operand_expr(operand);
                                            let value_field = self.encoder.encode_value_field(field_ty);
                                            state.substitute_value(&field_place.access(value_field), rhs_expr);
                                        },
                                    }
                                }
                            }

                            ref x => unimplemented!("{:?}", x)
                        }
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

            ref stmt => {
                unimplemented!("encoding of '{:?}'", stmt)
            }
        }
    }
}
