//! A MIR interpreter that translates MIR into vir_high expressions.

pub(super) mod state;

use self::state::ExprBackwardInterpreterState;
use crate::encoder::{
    errors::{EncodingResult, ErrorCtxt, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    high::{
        builtin_functions::{BuiltinFunctionHighKind, HighBuiltinFunctionEncoderInterface},
        pure_functions::HighPureFunctionEncoderInterface,
    },
    mir::{
        casts::CastsEncoderInterface,
        generics::MirGenericsEncoderInterface,
        places::PlacesEncoderInterface,
        pure::{PureFunctionEncoderInterface, SpecificationEncoderInterface},
        specifications::SpecificationsInterface,
        types::MirTypeEncoderInterface,
    },
    mir_encoder::MirEncoder,
    mir_interpreter::BackwardMirInterpreter,
    Encoder,
};
use log::{debug, trace};
use prusti_common::vir_high_local;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, ty, ty::subst::SubstsRef};
use rustc_span::Span;

use vir_crate::{
    common::expression::{BinaryOperationHelpers, UnaryOperationHelpers},
    high::{self as vir_high, operations::ty::Typed},
};

use super::PureEncodingContext;

// FIXME: Make this explicitly accessible only to spec_encoder and pure
// expression encoder.
pub(super) struct ExpressionBackwardInterpreter<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// MIR of the pure function being encoded.
    mir: &'p mir::Body<'tcx>,
    /// MirEncoder of the pure function being encoded.
    mir_encoder: MirEncoder<'p, 'v, 'tcx>,
    /// How panics are handled depending on the encoding context.
    pure_encoding_context: PureEncodingContext,
    /// DefId of the caller. Used for error reporting.
    caller_def_id: DefId,
    substs: SubstsRef<'tcx>,
}

/// This encoding works backward, so there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'v: 'p, 'tcx: 'v> ExpressionBackwardInterpreter<'p, 'v, 'tcx> {
    // FIXME: Make this explicitly accessible only to spec_encoder and pure
    // expression encoder.
    pub(in super::super) fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        mir: &'p mir::Body<'tcx>,
        def_id: DefId,
        pure_encoding_context: PureEncodingContext,
        caller_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> Self {
        Self {
            encoder,
            mir,
            mir_encoder: MirEncoder::new(encoder, mir, def_id),
            pure_encoding_context,
            caller_def_id,
            substs,
        }
    }

    fn encode_place(&self, place: mir::Place<'tcx>) -> SpannedEncodingResult<vir_high::Expression> {
        self.encoder.encode_place_high(self.mir, place)
    }

    fn encode_operand(
        &self,
        operand: &mir::Operand<'tcx>,
        span: Span,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        self.encoder
            .encode_operand_high(self.mir, operand)
            .with_span(span)
    }

    fn encode_binary_op(
        &self,
        op: mir::BinOp,
        left: vir_high::Expression,
        right: vir_high::Expression,
        ty: &vir_high::Type,
    ) -> EncodingResult<vir_high::Expression> {
        self.encoder.encode_binary_op_high(op, left, right, ty)
    }

    fn apply_assign_aggregate(
        &self,
        state: &mut ExprBackwardInterpreterState,
        ty: vir_high::Type,
        lhs: &vir_high::Expression,
        aggregate: &mir::AggregateKind<'tcx>,
        operands: &[mir::Operand<'tcx>],
        span: Span,
    ) -> SpannedEncodingResult<()> {
        let mut arguments = Vec::new();
        for operand in operands {
            let encoded_operand = self.encode_operand(operand, span)?;
            arguments.push(encoded_operand);
        }
        match aggregate {
            mir::AggregateKind::Array(_)
            | mir::AggregateKind::Tuple
            | mir::AggregateKind::Closure(_, _) => {
                let rhs = vir_high::Expression::constructor_no_pos(ty, arguments);
                state.substitute_value(lhs, rhs);
            }
            mir::AggregateKind::Adt(adt_did, variant_index, _, _, _) => {
                let tcx = self.encoder.env().tcx();
                let adt_def = tcx.adt_def(*adt_did);
                let ty_with_variant = if adt_def.variants().len() > 1 {
                    // FIXME: Shouls use adt_def.is_enum() as a check.
                    // FIXME: Most likely need to substitute the discriminant here.
                    let variant_def = &adt_def.variants()[*variant_index];
                    let variant_name = variant_def.ident(tcx).to_string();
                    ty.variant(variant_name.into())
                } else {
                    ty
                };
                let rhs = vir_high::Expression::constructor_no_pos(ty_with_variant, arguments);
                state.substitute_value(lhs, rhs);
            }
            mir::AggregateKind::Generator(_def_id, _subst, _) => {
                return Err(SpannedEncodingError::unsupported(
                    format!("Unsupported aggregate type: {:?}", aggregate),
                    span,
                ))
            }
        }
        Ok(())
    }

    fn apply_assign_statement(
        &self,
        state: &mut ExprBackwardInterpreterState,
        lhs: mir::Place<'tcx>,
        rhs: &mir::Rvalue<'tcx>,
        span: Span,
    ) -> SpannedEncodingResult<()> {
        let encoded_lhs = self.encode_place(lhs)?;
        let ty = self
            .encoder
            .encode_type_of_place_high(self.mir, lhs)
            .with_span(span)?;

        if !state.uses_place(&encoded_lhs) {
            // If the lhs is not mentioned in our state, do nothing
            trace!("The state does not mention {:?}", encoded_lhs);
            return Ok(());
        }

        match rhs {
            mir::Rvalue::Use(operand) => {
                let encoded_rhs = self.encode_operand(operand, span)?;
                state.substitute_value(&encoded_lhs, encoded_rhs);
            }
            mir::Rvalue::Aggregate(aggregate, operands) => {
                debug!("Encode aggregate {:?}, {:?}", aggregate, operands);
                self.apply_assign_aggregate(state, ty, &encoded_lhs, aggregate, operands, span)?
            }
            mir::Rvalue::BinaryOp(op, box (left, right)) => {
                let encoded_left = self.encode_operand(left, span)?;
                let encoded_right = self.encode_operand(right, span)?;
                let encoded_value = self
                    .encode_binary_op(*op, encoded_left, encoded_right, &ty)
                    .with_span(span)?;

                // Substitute a place of a value with an expression
                state.substitute_value(&encoded_lhs, encoded_value);
            }
            mir::Rvalue::CheckedBinaryOp(op, box (left, right)) => {
                let (operand_ty, check_ty) = if let vir_high::Type::Tuple(types) = ty {
                    (types.arguments[0].clone(), types.arguments[1].clone())
                } else {
                    unreachable!()
                };
                let encoded_left = self.encode_operand(left, span)?;
                let encoded_right = self.encode_operand(right, span)?;
                let encoded_value = self
                    .encode_binary_op(
                        *op,
                        encoded_left.clone(),
                        encoded_right.clone(),
                        &operand_ty,
                    )
                    .with_span(span)?;
                let encoded_check = self
                    .encoder
                    .encode_binary_op_check_high(*op, encoded_left, encoded_right, &operand_ty)
                    .with_span(span)?;
                let value_field = vir_high::FieldDecl::new("tuple_0".to_string(), operand_ty);
                let check_field = vir_high::FieldDecl::new("tuple_1".to_string(), check_ty);
                let lhs_value =
                    vir_high::Expression::field_no_pos(encoded_lhs.clone(), value_field);
                let lhs_check =
                    vir_high::Expression::field_no_pos(encoded_lhs.clone(), check_field);

                // Substitute a place of a value with an expression
                state.substitute_value(&lhs_value, encoded_value);
                state.substitute_value(&lhs_check, encoded_check);
            }
            mir::Rvalue::UnaryOp(op, operand) => {
                let encoded_operand = self.encode_operand(operand, span)?;
                let encoded_value = self
                    .encoder
                    .encode_unary_op_high(*op, encoded_operand, &ty)
                    .with_span(span)?;
                state.substitute_value(&encoded_lhs, encoded_value);
            }
            mir::Rvalue::Discriminant(src) => {
                let arg = self.encoder.encode_place_high(self.mir, *src)?;
                let expr = self
                    .encoder
                    .encode_discriminant_call(arg, encoded_lhs.get_type().clone())
                    .with_span(span)?;
                state.substitute_value(&encoded_lhs, expr);
            }
            mir::Rvalue::Ref(_, mir::BorrowKind::Unique, place)
            | mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place)
            | mir::Rvalue::Ref(_, mir::BorrowKind::Shared, place) => {
                let encoded_place = self.encoder.encode_place_high(self.mir, *place)?;
                let ty = self
                    .encoder
                    .encode_type_of_place_high(self.mir, *place)
                    .with_span(span)?;
                let pure_lifetime = vir_high::ty::LifetimeConst {
                    name: String::from("pure_erased"),
                };
                let encoded_ref = vir_high::Expression::addr_of_no_pos(
                    encoded_place,
                    vir_high::Type::reference(ty, pure_lifetime),
                );
                // Substitute the place
                state.substitute_value(&encoded_lhs, encoded_ref);
            }
            mir::Rvalue::Ref(_, kind, _) => {
                return Err(SpannedEncodingError::unsupported(
                    format!("unsupported kind of reference: {:?}", kind),
                    span,
                ));
            }
            mir::Rvalue::Cast(mir::CastKind::Misc, operand, dst_ty) => {
                let encoded_rhs = self.encoder.encode_cast_expression_high(
                    self.mir,
                    self.caller_def_id,
                    operand,
                    *dst_ty,
                    span,
                )?;
                state.substitute_value(&encoded_lhs, encoded_rhs);
            }
            mir::Rvalue::Cast(
                mir::CastKind::Pointer(ty::adjustment::PointerCast::Unsize),
                operand,
                cast_ty,
            ) => {
                if !cast_ty.is_slice() {
                    return Err(SpannedEncodingError::unsupported(
                        "unsizing a pointer or reference value is not supported",
                        span,
                    ));
                }
                // We have a cast of a slice or array into a slice.
                let arg = self.encode_operand(operand, span)?;
                let expr = self
                    .encoder
                    .encode_cast_into_slice(arg, ty)
                    .with_span(span)?;
                state.substitute_value(&encoded_lhs, expr);
            }
            mir::Rvalue::Cast(kind, _, _) => {
                return Err(SpannedEncodingError::unsupported(
                    format!("unsupported kind of cast: {:?}", kind),
                    span,
                ));
            }
            mir::Rvalue::Len(place) => {
                let arg = self.encoder.encode_place_high(self.mir, *place)?;
                let expr = self.encoder.encode_len_call(arg).with_span(span)?;
                state.substitute_value(&encoded_lhs, expr);
            }
            mir::Rvalue::Repeat(operand, times) => {
                let encoded_operand = self.encode_operand(operand, span)?;
                let len: usize = self
                    .encoder
                    .const_eval_intlike(times.val())
                    .with_span(span)?
                    .to_u64()
                    .unwrap()
                    .try_into()
                    .unwrap();
                let arguments = (0..len).map(|_| encoded_operand.clone()).collect();
                let expr = vir_high::Expression::constructor_no_pos(ty, arguments);
                state.substitute_value(&encoded_lhs, expr);
            }
            mir::Rvalue::ThreadLocalRef(..)
            | mir::Rvalue::AddressOf(..)
            | mir::Rvalue::ShallowInitBox(..)
            | mir::Rvalue::NullaryOp(..) => {
                return Err(SpannedEncodingError::unsupported(
                    format!("unsupported rvalue: {:?}", rhs),
                    span,
                ));
            }
        }

        Ok(())
    }

    fn apply_switch_int_terminator(
        &self,
        switch_ty: ty::Ty<'tcx>,
        discriminant: &mir::Operand<'tcx>,
        targets: &mir::SwitchTargets,
        states: FxHashMap<mir::BasicBlock, &ExprBackwardInterpreterState>,
        span: Span,
    ) -> SpannedEncodingResult<ExprBackwardInterpreterState> {
        trace!(
            "SwitchInt ty '{:?}', discr '{:?}', targets '{:?}'",
            switch_ty,
            discriminant,
            targets
        );
        let encoded_discriminant = self.encode_operand(discriminant, span)?;
        let mut cfg_targets = Vec::new();
        for (value, target) in targets.iter() {
            // Convert int to bool, if required
            let guard = match switch_ty.kind() {
                ty::TyKind::Bool => {
                    if value == 0 {
                        // If discr is 0 (false)
                        vir_high::Expression::not(encoded_discriminant.clone())
                    } else {
                        // If discr is not 0 (true)
                        encoded_discriminant.clone()
                    }
                }

                ty::TyKind::Int(_) | ty::TyKind::Uint(_) => vir_high::Expression::equals(
                    encoded_discriminant.clone(),
                    self.encoder
                        .encode_int_cast_high(value, switch_ty)
                        .with_span(span)?,
                ),

                ref x => unreachable!("{:?}", x),
            };
            cfg_targets.push((guard, target))
        }

        let default_target = targets.otherwise();
        let default_target_terminator = self.mir.basic_blocks()[default_target].terminator();
        trace!("default_target_terminator: {:?}", default_target_terminator);
        let default_is_unreachable = matches!(
            default_target_terminator.kind,
            mir::TerminatorKind::Unreachable
        );

        trace!("cfg_targets: {:?}", cfg_targets);

        let refined_default_target = if default_is_unreachable && !cfg_targets.is_empty() {
            // Here we can assume that the `cfg_targets` are exhaustive, and that
            // `default_target` is unreachable
            trace!("The default target is unreachable");
            cfg_targets.pop().unwrap().1
        } else {
            default_target
        };

        trace!("cfg_targets: {:?}", cfg_targets);

        let mut final_expr = states[&refined_default_target].expr().cloned();
        for (guard, target) in cfg_targets.into_iter() {
            if let Some(then_expr) = states[&target].expr() {
                final_expr = Some(if let Some(else_expr) = final_expr {
                    if then_expr == &else_expr {
                        // Optimization
                        else_expr
                    } else {
                        vir_high::Expression::conditional_no_pos(
                            guard,
                            then_expr.clone(),
                            else_expr,
                        )
                    }
                } else {
                    // Define `final_expr` for the first time
                    then_expr.clone()
                });
            }
        }

        Ok(ExprBackwardInterpreterState::new(final_expr))
    }

    fn apply_call_terminator(
        &self,
        args: &[mir::Operand<'tcx>],
        destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
        ty: ty::Ty<'tcx>,
        states: FxHashMap<mir::BasicBlock, &ExprBackwardInterpreterState>,
        span: Span,
    ) -> SpannedEncodingResult<ExprBackwardInterpreterState> {
        if let ty::TyKind::FnDef(def_id, call_substs) = ty.kind() {
            let def_id = *def_id;
            let full_func_proc_name: &str = &self.encoder.env().tcx().def_path_str(def_id);
            let func_proc_name = &self.encoder.env().get_item_name(def_id);

            // compose substitutions
            // TODO(tymap): do we need this?
            use crate::rustc_middle::ty::subst::Subst;
            let substs = call_substs.subst(self.encoder.env().tcx(), self.substs);

            let state = if let Some((lhs_place, target_block)) = destination {
                let encoded_lhs = self.encode_place(*lhs_place).with_span(span)?;
                let mut encoded_args: Vec<_> = args
                    .iter()
                    .map(|arg| self.encode_operand(arg, span))
                    .collect::<Result<_, _>>()
                    .with_span(span)?;
                match full_func_proc_name {
                    "prusti_contracts::old" => {
                        unimplemented!();
                        // self.encode_call_old()?
                    }
                    "prusti_contracts::before_expiry" => {
                        // self.encode_call_before_expiry()?
                        unimplemented!();
                    }
                    "std::cmp::PartialEq::eq" | "core::cmp::PartialEq::eq"
                        if self.has_structural_eq_impl(&args[0]).with_span(span)? =>
                    {
                        assert_eq!(args.len(), 2);
                        let encoded_rhs = vir_high::Expression::equals(
                            encoded_args[0].clone(),
                            encoded_args[1].clone(),
                        );
                        let mut state = states[target_block].clone();
                        state.substitute_value(&encoded_lhs, encoded_rhs);
                        state
                    }
                    "std::cmp::PartialEq::ne" | "core::cmp::PartialEq::ne"
                        if self.has_structural_eq_impl(&args[0]).with_span(span)? =>
                    {
                        assert_eq!(args.len(), 2);
                        let encoded_rhs = vir_high::Expression::not_equals(
                            encoded_args[0].clone(),
                            encoded_args[1].clone(),
                        );
                        let mut state = states[target_block].clone();
                        state.substitute_value(&encoded_lhs, encoded_rhs);
                        state
                    }
                    "core::slice::<impl [T]>::len" => {
                        assert_eq!(args.len(), 1);
                        self.encode_call_len(
                            *target_block,
                            states,
                            encoded_lhs,
                            encoded_args.pop().unwrap(),
                            span,
                        )?
                    }
                    "std::ops::IndexMut::index_mut"
                    | "core::ops::IndexMut::index_mut"
                    | "std::ops::Index::index"
                    | "core::ops::Index::index" => {
                        assert_eq!(args.len(), 2);
                        self.encode_call_index(
                            *target_block,
                            states,
                            encoded_lhs,
                            encoded_args[0].clone(),
                            encoded_args[1].clone(),
                            span,
                        )?
                    }

                    // Prusti-specific syntax
                    // TODO: check we are in a spec function
                    "prusti_contracts::exists"
                    | "prusti_contracts::forall"
                    | "prusti_contracts::specification_entailment"
                    | "prusti_contracts::call_description" => {
                        let expr = self.encoder.encode_prusti_operation_high(
                            full_func_proc_name,
                            span,
                            encoded_args,
                            self.caller_def_id,
                            substs,
                        )?;
                        let mut state = states[target_block].clone();
                        state.substitute_value(&encoded_lhs, expr);
                        state
                    }

                    _ => {
                        if self.encoder.is_pure(def_id) {
                            self.encode_call_generic(
                                *target_block,
                                states,
                                encoded_lhs,
                                def_id,
                                encoded_args,
                                span,
                                substs,
                            )?
                        } else {
                            return Err(SpannedEncodingError::incorrect(
                                format!(
                                    "use of impure function {:?} in pure code is not allowed",
                                    func_proc_name
                                ),
                                span,
                            ));
                        }
                    }
                }
            } else {
                // FIXME: Refactor the common code with the procedure encoder.

                // Encoding of a non-terminating function call
                let error_ctxt = match full_func_proc_name {
                    "std::rt::begin_panic"
                    | "core::panicking::panic"
                    | "core::panicking::panic_fmt"
                    | "std::rt::panic_fmt" => {
                        // This is called when a Rust assertion fails
                        // args[0]: message
                        // args[1]: position of failing assertions

                        let panic_cause = self.mir_encoder.encode_panic_cause(span);
                        ErrorCtxt::PanicInPureFunction(panic_cause)
                    }

                    _ => ErrorCtxt::DivergingCallInPureFunction,
                };
                let pos = self.encoder.error_manager().register_error(
                    span,
                    error_ctxt,
                    self.caller_def_id,
                );
                ExprBackwardInterpreterState::new_defined(
                    self.unreachable_expr(pos.into()).with_span(span)?,
                )
            };

            Ok(state)
        } else {
            // Other kind of calls?
            Err(SpannedEncodingError::unsupported(
                format!("unsupported type of call: {:?}", ty.kind()),
                span,
            ))
        }
    }

    fn encode_call_len(
        &self,
        target_block: mir::BasicBlock,
        states: FxHashMap<mir::BasicBlock, &ExprBackwardInterpreterState>,
        lhs: vir_high::Expression,
        arg: vir_high::Expression,
        span: Span,
    ) -> SpannedEncodingResult<ExprBackwardInterpreterState> {
        let expr = self.encoder.encode_len_call(arg).with_span(span)?;
        let mut state = states[&target_block].clone();
        state.substitute_value(&lhs, expr);
        Ok(state)
    }

    fn encode_call_index(
        &self,
        target_block: mir::BasicBlock,
        states: FxHashMap<mir::BasicBlock, &ExprBackwardInterpreterState>,
        lhs: vir_high::Expression,
        container: vir_high::Expression,
        index: vir_high::Expression,
        span: Span,
    ) -> SpannedEncodingResult<ExprBackwardInterpreterState> {
        let expr = self
            .encoder
            .encode_subslice_call(container, index)
            .with_span(span)?;
        let mut state = states[&target_block].clone();
        state.substitute_value(&lhs, expr);
        Ok(state)
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_call_generic(
        &self,
        target_block: mir::BasicBlock,
        states: FxHashMap<mir::BasicBlock, &ExprBackwardInterpreterState>,
        lhs: vir_high::Expression,
        def_id: DefId,
        args: Vec<vir_high::Expression>,
        span: Span,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<ExprBackwardInterpreterState> {
        let (function_name, return_type) = self
            .encoder
            .encode_pure_function_use_high(def_id, self.caller_def_id, substs)
            .with_span(span)?;
        trace!("Encoding pure function call '{}'", function_name);
        let pos = self.encoder.error_manager().register_error(
            span,
            ErrorCtxt::PureFunctionCall,
            self.caller_def_id,
        );
        let type_arguments = self
            .encoder
            .encode_generic_arguments_high(def_id, substs)
            .with_span(span)?;
        let encoded_rhs =
            vir_high::Expression::function_call(function_name, type_arguments, args, return_type)
                .set_default_position(pos.into());
        let mut state = states[&target_block].clone();
        state.substitute_value(&lhs, encoded_rhs);
        Ok(state)
    }

    fn unreachable_expr(
        &self,
        position: vir_high::Position,
    ) -> EncodingResult<vir_high::Expression> {
        let ty = self.encoder.encode_type_high(self.mir.return_ty())?;
        let encoded_type = self.encoder.encode_type_high(self.mir.return_ty())?;
        let (function_name, type_arguments) = self
            .encoder
            .encode_builtin_function_use_high(BuiltinFunctionHighKind::Unreachable(encoded_type))?;
        Ok(vir_high::Expression::func_app(
            function_name,
            type_arguments,
            Vec::new(),
            Vec::new(),
            ty,
            position,
        ))
    }

    fn undefined_expr(&self, position: vir_high::Position) -> EncodingResult<vir_high::Expression> {
        let ty = self.encoder.encode_type_high(self.mir.return_ty())?;
        let encoded_type = self.encoder.encode_type_high(self.mir.return_ty())?;
        let (function_name, type_arguments) = self
            .encoder
            .encode_builtin_function_use_high(BuiltinFunctionHighKind::Undefined(encoded_type))?;
        Ok(vir_high::Expression::func_app(
            function_name,
            type_arguments,
            Vec::new(),
            Vec::new(),
            ty,
            position,
        ))
    }

    fn has_structural_eq_impl(&self, operand: &mir::Operand<'tcx>) -> EncodingResult<bool> {
        let ty = self.encoder.get_operand_type(self.mir, operand)?;
        Ok(self.encoder.has_structural_eq_impl(ty))
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> BackwardMirInterpreter<'tcx>
    for ExpressionBackwardInterpreter<'p, 'v, 'tcx>
{
    type State = ExprBackwardInterpreterState;
    type Error = SpannedEncodingError;

    fn apply_terminator(
        &self,
        _bb: mir::BasicBlock,
        terminator: &mir::Terminator<'tcx>,
        states: FxHashMap<mir::BasicBlock, &Self::State>,
    ) -> Result<Self::State, Self::Error> {
        use rustc_middle::mir::TerminatorKind;
        let span = terminator.source_info.span;
        let state = match &terminator.kind {
            TerminatorKind::Unreachable => {
                assert!(states.is_empty());
                let pos = self.encoder.error_manager().register_error(
                    span,
                    ErrorCtxt::Unexpected,
                    self.caller_def_id,
                );
                ExprBackwardInterpreterState::new_defined(
                    self.undefined_expr(pos.into()).with_span(span)?,
                )
            }

            TerminatorKind::Abort | TerminatorKind::Resume { .. } => {
                assert!(states.is_empty());
                let pos = self
                    .encoder
                    .error_manager()
                    .register_error(span, ErrorCtxt::Unexpected, self.caller_def_id)
                    .into();
                ExprBackwardInterpreterState::new_defined(
                    self.unreachable_expr(pos).with_span(span)?,
                )
            }

            TerminatorKind::Drop { target, .. } => {
                assert!(!states.is_empty() && states.len() <= 2);
                states[target].clone()
            }

            TerminatorKind::Goto { ref target } => {
                assert_eq!(states.len(), 1);
                states[target].clone()
            }

            TerminatorKind::FalseEdge { real_target, .. } => {
                assert_eq!(states.len(), 2);
                states[real_target].clone()
            }

            TerminatorKind::FalseUnwind { real_target, .. } => {
                assert_eq!(states.len(), 1);
                states[real_target].clone()
            }

            TerminatorKind::Return => {
                assert!(states.is_empty());
                debug!("Return type: {:?}", self.mir.return_ty());
                let return_type = self
                    .encoder
                    .encode_type_high(self.mir.return_ty())
                    .with_span(span)?;
                let return_var = vir_high_local! { _0: {return_type} };
                ExprBackwardInterpreterState::new_defined(vir_high::Expression::local_no_pos(
                    return_var,
                ))
            }

            TerminatorKind::SwitchInt {
                switch_ty,
                discr,
                targets,
            } => self.apply_switch_int_terminator(*switch_ty, discr, targets, states, span)?,

            TerminatorKind::DropAndReplace { .. } => unimplemented!(),

            TerminatorKind::Call {
                args,
                destination,
                func: mir::Operand::Constant(box mir::Constant { literal, .. }),
                ..
            } => self.apply_call_terminator(args, destination, literal.ty(), states, span)?,

            TerminatorKind::Call { .. } => {
                return Err(SpannedEncodingError::unsupported(
                    "unsupported kind of call",
                    span,
                ));
            }

            TerminatorKind::Assert {
                cond,
                expected,
                target,
                msg,
                ..
            } => {
                let encoded_condition = self.encode_operand(cond, span)?;
                let guard = if *expected {
                    encoded_condition
                } else {
                    vir_high::Expression::not(encoded_condition)
                };

                let error_ctxt = if let mir::AssertKind::BoundsCheck { .. } = msg {
                    ErrorCtxt::BoundsCheckAssert
                } else {
                    let assert_msg = msg.description().to_string();
                    ErrorCtxt::PureFunctionAssertTerminator(assert_msg)
                };

                let pos = self.encoder.error_manager().register_error(
                    terminator.source_info.span,
                    error_ctxt,
                    self.caller_def_id,
                );

                match self.pure_encoding_context {
                    PureEncodingContext::Trigger => {
                        // We are encoding a trigger, so all panic branches must be stripped.
                        states[target].clone()
                    }
                    PureEncodingContext::Assertion => {
                        // We are encoding an assertion, so all failures should be equivalent to false.
                        debug_assert!(matches!(self.mir.return_ty().kind(), ty::TyKind::Bool));
                        ExprBackwardInterpreterState::new(states[target].expr().map(
                            |target_expr| {
                                vir_high::Expression::conditional_no_pos(
                                    guard.clone(),
                                    target_expr.clone(),
                                    false.into(),
                                )
                            },
                        ))
                    }
                    PureEncodingContext::Code => {
                        // We are encoding a pure function, so all failures should be unreachable.
                        let failure_encoding = self.unreachable_expr(pos.into()).with_span(span)?;
                        ExprBackwardInterpreterState::new(states[target].expr().map(
                            |target_expr| {
                                vir_high::Expression::conditional_no_pos(
                                    guard.clone(),
                                    target_expr.clone(),
                                    failure_encoding,
                                )
                            },
                        ))
                    }
                }
            }

            TerminatorKind::Yield { .. }
            | TerminatorKind::GeneratorDrop
            | TerminatorKind::InlineAsm { .. } => {
                return Err(SpannedEncodingError::unsupported(
                    format!(
                        "unsupported terminator kind inside a pure expression: {:?}",
                        terminator.kind
                    ),
                    span,
                ))
            }
        };

        // self.apply_downcasts(&mut state, location)?; FIXME: Is this needed?

        Ok(state)
    }

    fn apply_statement(
        &self,
        bb: mir::BasicBlock,
        stmt_index: usize,
        statement: &mir::Statement<'tcx>,
        state: &mut Self::State,
    ) -> Result<(), Self::Error> {
        trace!("apply_statement {:?}, state: {}", statement, state);
        let span = statement.source_info.span;
        let location = mir::Location {
            block: bb,
            statement_index: stmt_index,
        };
        match &statement.kind {
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..)
            | mir::StatementKind::FakeRead(..) => {
                // Nothing to do
            }
            mir::StatementKind::Assign(box (lhs, rhs)) => {
                self.apply_assign_statement(state, *lhs, rhs, span)?;
            }
            kind => {
                unimplemented!("kind: {:?} at {:?}", kind, location);
            }
        }

        // self.apply_downcasts(state, location)?; FIXME: Is this needed?

        Ok(())
    }
}
