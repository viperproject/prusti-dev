use super::interface::PureFunctionEncoderInterface;
use crate::encoder::{
    builtin_encoder::BuiltinFunctionKind,
    errors::{EncodingResult, ErrorCtxt, SpannedEncodingError, SpannedEncodingResult, WithSpan},
    high::{
        builtin_functions::HighBuiltinFunctionEncoderInterface,
        generics::HighGenericsEncoderInterface, types::HighTypeEncoderInterface,
    },
    mir::{
        pure::{specifications::SpecificationEncoderInterface, PureEncodingContext},
        sequences::MirSequencesEncoderInterface,
        specifications::SpecificationsInterface,
        types::MirTypeEncoderInterface,
    },
    mir_encoder::{MirEncoder, PlaceEncoder, PlaceEncoding, PRECONDITION_LABEL, WAND_LHS_LABEL},
    mir_interpreter::{BackwardMirInterpreter, ExprBackwardInterpreterState},
    snapshot::interface::SnapshotEncoderInterface,
    Encoder,
};
use log::{debug, trace};
use prusti_common::vir_local;
use prusti_interface::environment::mir_utils::SliceOrArrayRef;
use prusti_rustc_interface::{
    hir::def_id::DefId,
    middle::{mir, span_bug, ty},
};
use rustc_hash::FxHashMap;
use std::{convert::TryInto, mem};
use vir_crate::polymorphic::{self as vir};

pub(crate) struct PureFunctionBackwardInterpreter<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// MIR of the pure function being encoded.
    mir: &'p mir::Body<'tcx>,
    /// MirEncoder of the pure function being encoded.
    mir_encoder: MirEncoder<'p, 'v, 'tcx>,
    /// How panics are handled depending on the encoding context.
    pure_encoding_context: PureEncodingContext,
    /// DefId of the caller. Used for error reporting.
    caller_def_id: DefId,
    def_id: DefId, // TODO(tymap): is this actually caller_def_id?
}

/// This encoding works backward, so there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'v: 'p, 'tcx: 'v> PureFunctionBackwardInterpreter<'p, 'v, 'tcx> {
    pub(crate) fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        mir: &'p mir::Body<'tcx>,
        def_id: DefId,
        pure_encoding_context: PureEncodingContext,
        caller_def_id: DefId,
    ) -> Self {
        PureFunctionBackwardInterpreter {
            encoder,
            mir,
            mir_encoder: MirEncoder::new(encoder, mir, def_id),
            pure_encoding_context,
            caller_def_id,
            def_id,
        }
    }

    /// Wrap all expressions contained in the state with downcast information to be used by the
    /// fold-unfold pass.
    fn apply_downcasts(
        &self,
        state: &mut ExprBackwardInterpreterState,
        location: mir::Location,
    ) -> SpannedEncodingResult<()> {
        let span = self.mir_encoder.get_span_of_location(location);
        if let Some(expr) = state.expr_mut() {
            let downcasts = self.mir_encoder.get_downcasts_at_location(location);
            // Reverse `downcasts` because the encoding works backward
            for (place, variant_idx) in downcasts.into_iter().rev() {
                let (encoded_place, place_ty, _) = self
                    .encode_projection(place.local, &place.projection[..])
                    .with_span(span)?;
                let variant_field = if let ty::TyKind::Adt(adt_def, _subst) = place_ty.kind() {
                    let tcx = self.encoder.env().tcx();
                    let variant_name = adt_def.variants()[variant_idx].ident(tcx).to_string();
                    self.encoder.encode_enum_variant_field(&variant_name)
                } else {
                    unreachable!()
                };
                // Replace two times to avoid cloning `expr`, which could be big.
                let base = mem::replace(expr, true.into());
                let new_expr = vir::Expr::downcast(base, encoded_place, variant_field);
                let _ = mem::replace(expr, new_expr);
            }
        }
        Ok(())
    }

    pub(crate) fn mir_encoder(&self) -> &MirEncoder<'p, 'v, 'tcx> {
        &self.mir_encoder
    }

    fn encode_place(
        &self,
        place: mir::Place<'tcx>,
    ) -> EncodingResult<(vir::Expr, ty::Ty<'tcx>, Option<usize>)> {
        let (encoded_place, ty, variant_idx) = self.mir_encoder.encode_place(place)?;
        let encoded_expr = self.postprocess_place_encoding(encoded_place)?;
        Ok((encoded_expr, ty, variant_idx))
    }

    fn encode_projection(
        &self,
        local: mir::Local,
        projection: &[mir::PlaceElem<'tcx>],
    ) -> EncodingResult<(vir::Expr, ty::Ty<'tcx>, Option<usize>)> {
        let (encoded_place, ty, variant_idx) =
            self.mir_encoder.encode_projection(local, projection)?;
        let encoded_expr = self.postprocess_place_encoding(encoded_place)?;
        Ok((encoded_expr, ty, variant_idx))
    }

    fn encode_operand(&self, operand: &mir::Operand<'tcx>) -> EncodingResult<(vir::Expr, bool)> {
        // TODO: De-duplicate with mir_encoder.encode_operand_place.
        //   Maybe returning `None` from mir_encoder.encode_operand_place for arrays in general?
        match operand {
            &mir::Operand::Move(place) | &mir::Operand::Copy(place) => {
                Ok((self.encode_place(place)?.0, false))
            }
            mir::Operand::Constant(constant) => {
                Ok((self.encoder.encode_snapshot_constant(constant)?, true))
            }
        }
    }

    fn postprocess_place_encoding(
        &self,
        place_encoding: PlaceEncoding<'tcx>,
    ) -> EncodingResult<vir::Expr> {
        Ok(match place_encoding {
            PlaceEncoding::Expr(e) => e,
            PlaceEncoding::FieldAccess { box base, field } => {
                let postprocessed_base = self.postprocess_place_encoding(base)?;
                postprocessed_base.field(field)
            }
            PlaceEncoding::Variant { box base, field } => {
                let postprocessed_base = self.postprocess_place_encoding(base)?;
                vir::Expr::Variant(vir::Variant {
                    base: box postprocessed_base,
                    variant_index: field,
                    position: vir::Position::default(),
                })
            }
            PlaceEncoding::ArrayAccess {
                box base,
                index,
                rust_array_ty,
                ..
            } => {
                let postprocessed_base = self.postprocess_place_encoding(base)?;
                let idx_val_int = self.encoder.patch_snapshots(vir::Expr::snap_app(index))?;

                self.encoder.encode_snapshot_array_idx(
                    rust_array_ty,
                    postprocessed_base,
                    idx_val_int,
                )?
            }
            PlaceEncoding::SliceAccess {
                box base,
                index,
                rust_slice_ty,
                ..
            } => {
                let postprocessed_base = self.postprocess_place_encoding(base)?;
                let idx_val_int = self.encoder.patch_snapshots(vir::Expr::snap_app(index))?;

                self.encoder.encode_snapshot_slice_idx(
                    rust_slice_ty,
                    postprocessed_base,
                    idx_val_int,
                )?
            }
        })
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> BackwardMirInterpreter<'tcx>
    for PureFunctionBackwardInterpreter<'p, 'v, 'tcx>
{
    type State = ExprBackwardInterpreterState;
    type Error = SpannedEncodingError;

    fn apply_terminator(
        &self,
        bb: mir::BasicBlock,
        term: &mir::Terminator<'tcx>,
        states: FxHashMap<mir::BasicBlock, &Self::State>,
    ) -> Result<Self::State, Self::Error> {
        trace!("apply_terminator {:?}, states: {:?}", term, states);
        use prusti_rustc_interface::middle::mir::TerminatorKind;
        let span = term.source_info.span;
        let location = self.mir.terminator_loc(bb);

        // Generate a function call that leaves the expression undefined.
        let unreachable_expr = |pos| {
            self.encoder
                .encode_snapshot_type(self.mir.return_ty())
                .map(|encoded_type| {
                    let (function_name, type_arguments) =
                        self.encoder
                            .encode_builtin_function_use(BuiltinFunctionKind::Unreachable(
                                encoded_type.clone(),
                            ));
                    vir::Expr::func_app(
                        function_name,
                        type_arguments,
                        vec![],
                        vec![],
                        encoded_type,
                        pos,
                    )
                })
        };

        // Generate a function call that leaves the expression undefined.
        let undef_expr = |pos| {
            self.encoder
                .encode_snapshot_type(self.mir.return_ty())
                .map(|encoded_type| {
                    let (function_name, type_arguments) =
                        self.encoder
                            .encode_builtin_function_use(BuiltinFunctionKind::Undefined(
                                encoded_type.clone(),
                            ));
                    vir::Expr::func_app(
                        function_name,
                        type_arguments,
                        vec![],
                        vec![],
                        encoded_type,
                        pos,
                    )
                })
        };

        let mut state = match term.kind {
            TerminatorKind::Unreachable => {
                assert!(states.is_empty());
                let pos = self.encoder.error_manager().register_error(
                    term.source_info.span,
                    ErrorCtxt::Unexpected,
                    self.caller_def_id,
                );
                ExprBackwardInterpreterState::new_defined(
                    undef_expr(pos).with_span(term.source_info.span)?,
                )
            }

            TerminatorKind::Abort | TerminatorKind::Resume { .. } => {
                assert!(states.is_empty());
                let pos = self.encoder.error_manager().register_error(
                    term.source_info.span,
                    ErrorCtxt::Unexpected,
                    self.caller_def_id,
                );
                ExprBackwardInterpreterState::new_defined(
                    unreachable_expr(pos).with_span(term.source_info.span)?,
                )
            }

            TerminatorKind::Drop { ref target, .. } => {
                assert!(!states.is_empty() && states.len() <= 2);
                states[target].clone()
            }

            TerminatorKind::Goto { ref target } => {
                assert_eq!(states.len(), 1);
                states[target].clone()
            }

            TerminatorKind::FalseEdge {
                ref real_target, ..
            } => {
                assert_eq!(states.len(), 2);
                states[real_target].clone()
            }

            TerminatorKind::FalseUnwind {
                ref real_target, ..
            } => {
                assert_eq!(states.len(), 1);
                states[real_target].clone()
            }

            TerminatorKind::Return => {
                assert!(states.is_empty());
                trace!("Return type: {:?}", self.mir.return_ty());
                let return_type = self
                    .encoder
                    .encode_type(self.mir.return_ty())
                    .with_span(span)?;
                let return_var = vir_local! { _0: {return_type} };
                ExprBackwardInterpreterState::new_defined(
                    self.encoder
                        .encode_value_expr(vir::Expr::local(return_var), self.mir.return_ty())
                        .with_span(span)?,
                )
            }

            TerminatorKind::SwitchInt {
                switch_ty,
                ref discr,
                ref targets,
            } => {
                trace!(
                    "SwitchInt ty '{:?}', discr '{:?}', targets '{:?}'",
                    switch_ty,
                    discr,
                    targets
                );
                let mut cfg_targets: Vec<(vir::Expr, mir::BasicBlock)> = vec![];
                let discr_val = self
                    .mir_encoder
                    .encode_operand_expr(discr)
                    .with_span(span)?;
                for (value, target) in targets.iter() {
                    // Convert int to bool, if required
                    let viper_guard = match switch_ty.kind() {
                        ty::TyKind::Bool => {
                            if value == 0 {
                                // If discr is 0 (false)
                                vir::Expr::not(discr_val.clone())
                            } else {
                                // If discr is not 0 (true)
                                discr_val.clone()
                            }
                        }

                        ty::TyKind::Int(_) | ty::TyKind::Uint(_) => vir::Expr::eq_cmp(
                            discr_val.clone(),
                            self.encoder.encode_int_cast(value, switch_ty),
                        ),

                        ref x => unreachable!("{:?}", x),
                    };
                    cfg_targets.push((viper_guard, target))
                }
                let default_target = targets.otherwise();

                let default_target_terminator = self.mir.basic_blocks()[default_target]
                    .terminator
                    .as_ref()
                    .unwrap();
                trace!("default_target_terminator: {:?}", default_target_terminator);
                let default_is_unreachable =
                    matches!(default_target_terminator.kind, TerminatorKind::Unreachable);

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
                                vir::Expr::ite(guard, then_expr.clone(), else_expr)
                            }
                        } else {
                            // Define `final_expr` for the first time
                            then_expr.clone()
                        });
                    }
                }
                ExprBackwardInterpreterState::new(final_expr)
            }

            TerminatorKind::DropAndReplace { .. } => unimplemented!(),

            TerminatorKind::Call {
                ref args,
                destination,
                target,
                func: mir::Operand::Constant(ref const_func),
                ..
            } => {
                let ty = const_func.ty();
                if let ty::TyKind::FnDef(def_id, call_substs) = ty.kind() {
                    trace!(
                        "apply_terminator for function call {:?} with substs {:?}",
                        def_id,
                        call_substs
                    );
                    let def_id = *def_id;
                    let tcx = self.encoder.env().tcx();
                    let full_func_proc_name: &str = &tcx.def_path_str(def_id);
                    let func_proc_name = &self.encoder.env().get_item_name(def_id);

                    let state = if let Some(target_block) = target {
                        let (encoded_lhs, ty, _) =
                            self.encode_place(destination).with_span(span)?;
                        let encoded_args: Vec<vir::Expr> = args
                            .iter()
                            .map(|arg| self.mir_encoder.encode_operand_expr(arg))
                            .collect::<Result<_, _>>()
                            .with_span(span)?;

                        match full_func_proc_name {
                            "prusti_contracts::old" => {
                                trace!("Encoding old expression {:?}", args[0]);
                                assert_eq!(args.len(), 1);

                                // Return an error for unsupported old(..) types

                                let encoded_rhs = self.mir_encoder.encode_old_expr(
                                    vir::Expr::snap_app(encoded_args[0].clone()),
                                    PRECONDITION_LABEL,
                                );
                                let mut state = states[&target_block].clone();
                                state.substitute_value(&encoded_lhs, encoded_rhs);
                                state
                            }

                            "prusti_contracts::before_expiry" => {
                                trace!("Encoding before_expiry expression {:?}", args[0]);
                                assert_eq!(args.len(), 1);
                                let encoded_rhs = self.mir_encoder.encode_old_expr(
                                    vir::Expr::snap_app(encoded_args[0].clone()),
                                    WAND_LHS_LABEL,
                                );
                                let mut state = states[&target_block].clone();
                                state.substitute_value(&encoded_lhs, encoded_rhs);
                                state
                            }

                            "std::cmp::PartialEq::eq" | "core::cmp::PartialEq::eq"
                                if self.encoder.has_structural_eq_impl(
                                    self.mir_encoder.get_operand_ty(&args[0]),
                                ) =>
                            {
                                assert_eq!(args.len(), 2);
                                let encoded_rhs = vir::Expr::eq_cmp(
                                    vir::Expr::snap_app(encoded_args[0].clone()),
                                    vir::Expr::snap_app(encoded_args[1].clone()),
                                );
                                let mut state = states[&target_block].clone();
                                state.substitute_value(&encoded_lhs, encoded_rhs);
                                state
                            }

                            "std::cmp::PartialEq::ne" | "core::cmp::PartialEq::ne"
                                if self.encoder.has_structural_eq_impl(
                                    self.mir_encoder.get_operand_ty(&args[0]),
                                ) =>
                            {
                                assert_eq!(args.len(), 2);
                                let encoded_rhs = vir::Expr::ne_cmp(
                                    vir::Expr::snap_app(encoded_args[0].clone()),
                                    vir::Expr::snap_app(encoded_args[1].clone()),
                                );
                                let mut state = states[&target_block].clone();
                                state.substitute_value(&encoded_lhs, encoded_rhs);
                                state
                            }

                            "core::slice::<impl [T]>::len" => {
                                assert_eq!(args.len(), 1);
                                let slice_ty = self.mir_encoder.get_operand_ty(&args[0]);
                                let len = self
                                    .encoder
                                    .encode_snapshot_slice_len(slice_ty, encoded_args[0].clone())
                                    .with_span(span)?;

                                let mut state = states[&target_block].clone();
                                state.substitute_value(&encoded_lhs, len);
                                state
                            }

                            "std::ops::Index::index" | "core::ops::Index::index" => {
                                assert_eq!(args.len(), 2);
                                trace!("slice::index(args={:?}, encoded_args={:?}, ty={:?}, encoded_lhs={:?})", args, encoded_args, ty, encoded_lhs);

                                let base_ty = self.mir_encoder.get_operand_ty(&args[0]);

                                let idx_ty = self.mir_encoder.get_operand_ty(&args[1]);
                                let idx_ty_did = match idx_ty.ty_adt_def() {
                                    Some(def) => def.did(),
                                    None => return Err(SpannedEncodingError::unsupported(
                                        format!("Using {} as index/range type for {} is not currently supported in pure functions", idx_ty, base_ty),
                                        span,
                                    ))
                                };
                                let idx_ident = tcx.def_path_str(idx_ty_did);
                                let encoded_idx = &encoded_args[1];

                                // TODO: what do we actually do here? this seems a littly hacky.
                                // there's fields like _5.f$start.val_int on `encoded_idx`, it just feels hacky to
                                // manually re-do them here when we probably just encoded the type and the
                                // construction of the fields..
                                // Also, duplication with procedure_encoder.rs
                                let usize_ty = tcx.mk_ty(ty::TyKind::Uint(ty::UintTy::Usize));
                                let start = match &*idx_ident {
                                    "std::ops::Range" | "core::ops::Range" |
                                    "std::ops::RangeFrom" | "core::ops::RangeFrom" =>
                                        self.encoder.encode_struct_field_value(encoded_idx.clone(), "start", usize_ty).with_span(span)?,
                                    // See procedure_encoder.rs
                                    "std::ops::RangeInclusive" | "core::ops::RangeInclusive" => return Err(
                                        SpannedEncodingError::unsupported("slicing with RangeInclusive (e.g. [x..=y]) currently not supported".to_string(), span)
                                    ),
                                    "std::ops::RangeTo" | "core::ops::RangeTo" |
                                    "std::ops::RangeFull" | "core::ops::RangeFull" |
                                    "std::ops::RangeToInclusive" | "core::ops::RangeToInclusive" => vir::Expr::from(0u32),
                                    _ => unreachable!("{}", idx_ident)
                                };
                                let end = match &*idx_ident {
                                    "std::ops::Range" | "core::ops::Range" |
                                    "std::ops::RangeTo" | "core::ops::RangeTo" =>
                                        self.encoder.encode_struct_field_value(encoded_idx.clone(), "end", usize_ty).with_span(span)?,
                                    "std::ops::RangeInclusive" | "core::ops::RangeInclusive" => return Err(
                                        SpannedEncodingError::unsupported("slicing with RangeInclusive (e.g. [x..=y]) currently not supported".to_string(), span)
                                    ),
                                    "std::ops::RangeToInclusive" | "core::ops::RangeToInclusive" => {
                                        let end_expr = self.encoder.encode_struct_field_value(encoded_idx.clone(), "end", usize_ty).with_span(span)?;
                                        vir::Expr::add(end_expr, vir::Expr::from(1u32))
                                    }
                                    "std::ops::RangeFrom" | "core::ops::RangeFrom" |
                                    "std::ops::RangeFull" | "core::ops::RangeFull" => {
                                        if base_ty.peel_refs().is_array() {
                                            let array_len = self.encoder.encode_sequence_types(base_ty.peel_refs()).with_span(span)?.sequence_len.unwrap();
                                            vir::Expr::from(array_len)
                                        } else if base_ty.is_slice() {
                                            let base = self.mir_encoder.encode_operand_place(&args[0]).with_span(span)?.unwrap();
                                            let base_expr = self.encoder.encode_value_expr(base, base_ty).with_span(span)?;
                                            let slice_types_base = self.encoder.encode_sequence_types(base_ty.peel_refs()).with_span(span)?;
                                            slice_types_base.len(self.encoder, base_expr)
                                        } else { todo!("Get last idx for {}", base_ty) }
                                    }
                                    _ => unreachable!("{}", idx_ident)
                                };

                                let slice_expr = self
                                    .encoder
                                    .encode_snapshot_slicing(
                                        base_ty,
                                        encoded_args[0].clone(),
                                        ty,
                                        start,
                                        end,
                                    )
                                    .with_span(span)?;

                                let mut state = states[&target_block].clone();
                                state.substitute_value(&encoded_lhs, slice_expr);
                                state
                            }

                            // Prusti-specific syntax
                            // TODO: check we are in a spec function
                            "prusti_contracts::implication"
                            | "prusti_contracts::exists"
                            | "prusti_contracts::forall"
                            | "prusti_contracts::specification_entailment"
                            | "prusti_contracts::call_description" => {
                                let expr = self.encoder.encode_prusti_operation(
                                    full_func_proc_name,
                                    span,
                                    encoded_args,
                                    self.caller_def_id,
                                    call_substs,
                                )?;
                                let mut state = states[&target_block].clone();
                                state.substitute_value(&encoded_lhs, expr);
                                state
                            }

                            // simple function call
                            _ => {
                                let (called_def_id, call_substs) = self
                                    .encoder
                                    .env()
                                    .resolve_method_call(self.def_id, def_id, call_substs);
                                trace!("Resolved function call: {:?}", called_def_id);

                                let is_pure_function =
                                    self.encoder.is_pure(called_def_id, Some(call_substs));
                                let (function_name, return_type) = if is_pure_function {
                                    self.encoder
                                        .encode_pure_function_use(
                                            called_def_id,
                                            self.caller_def_id,
                                            call_substs,
                                        )
                                        .with_span(term.source_info.span)?
                                } else {
                                    return Err(SpannedEncodingError::incorrect(
                                        format!(
                                            "use of impure function {:?} in pure code is not allowed",
                                            func_proc_name
                                        ),
                                        term.source_info.span,
                                    ));
                                };
                                trace!("Encoding pure function call '{}'", function_name);

                                let formal_args: Vec<vir::LocalVar> = args
                                    .iter()
                                    .enumerate()
                                    .map(|(i, arg)| {
                                        self.mir_encoder
                                            .encode_operand_expr_type(arg)
                                            .map(|ty| vir::LocalVar::new(format!("x{}", i), ty))
                                    })
                                    .collect::<Result<_, _>>()
                                    .with_span(term.source_info.span)?;

                                let pos = self.encoder.error_manager().register_error(
                                    term.source_info.span,
                                    ErrorCtxt::PureFunctionCall,
                                    self.caller_def_id,
                                );
                                let type_arguments = self
                                    .encoder
                                    .encode_generic_arguments(called_def_id, call_substs)
                                    .with_span(term.source_info.span)?;
                                let encoded_rhs = vir::Expr::func_app(
                                    function_name,
                                    type_arguments,
                                    encoded_args,
                                    formal_args,
                                    return_type,
                                    pos,
                                );
                                let mut state = states[&target_block].clone();
                                state.substitute_value(&encoded_lhs, encoded_rhs);
                                state
                            }
                        }
                    } else {
                        // Encoding of a non-terminating function call
                        // FIXME: Refactor the common code with the procedure encoder.
                        match self.pure_encoding_context {
                            PureEncodingContext::Trigger => {
                                // We are encoding a trigger, so all panic branches must be stripped.
                                ExprBackwardInterpreterState::new(None)
                            }
                            PureEncodingContext::Assertion => {
                                // We are encoding an assertion, so all failures should be equivalent to false.
                                debug_assert!(matches!(
                                    self.mir.return_ty().kind(),
                                    ty::TyKind::Bool
                                ));
                                ExprBackwardInterpreterState::new(Some(false.into()))
                            }
                            PureEncodingContext::Code => {
                                // We are encoding a pure function, so all failures should be unreachable.
                                let error_ctxt = match full_func_proc_name {
                                    "std::rt::begin_panic"
                                    | "core::panicking::panic"
                                    | "core::panicking::panic_fmt" => {
                                        // This is called when a Rust assertion fails
                                        // args[0]: message
                                        // args[1]: position of failing assertions

                                        let panic_cause = self.mir_encoder.encode_panic_cause(span);
                                        ErrorCtxt::PanicInPureFunction(panic_cause)
                                    }

                                    _ => ErrorCtxt::DivergingCallInPureFunction,
                                };
                                let pos = self.encoder.error_manager().register_error(
                                    term.source_info.span,
                                    error_ctxt,
                                    self.caller_def_id,
                                );
                                ExprBackwardInterpreterState::new_defined(
                                    unreachable_expr(pos).with_span(term.source_info.span)?,
                                )
                            }
                        }
                    };

                    state
                } else {
                    // Other kind of calls?
                    unimplemented!();
                }
            }

            TerminatorKind::Call { .. } => {
                // Other kind of calls?
                unimplemented!();
            }

            TerminatorKind::Assert {
                ref cond,
                expected,
                ref target,
                ref msg,
                ..
            } => {
                let cond_val = self.mir_encoder.encode_operand_expr(cond).with_span(span)?;
                let viper_guard = if expected {
                    cond_val
                } else {
                    vir::Expr::not(cond_val)
                };

                let error_ctxt = if let mir::AssertKind::BoundsCheck { .. } = msg {
                    ErrorCtxt::BoundsCheckAssert
                } else {
                    let assert_msg = msg.description().to_string();
                    ErrorCtxt::PureFunctionAssertTerminator(assert_msg)
                };

                let pos = self.encoder.error_manager().register_error(
                    term.source_info.span,
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
                                vir::Expr::ite(
                                    viper_guard.clone(),
                                    target_expr.clone(),
                                    false.into(),
                                )
                            },
                        ))
                    }
                    PureEncodingContext::Code => {
                        // We are encoding a pure function, so all failures should be unreachable.
                        let failure_encoding =
                            unreachable_expr(pos).with_span(term.source_info.span)?;
                        ExprBackwardInterpreterState::new(states[target].expr().map(
                            |target_expr| {
                                vir::Expr::ite(
                                    viper_guard.clone(),
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
                unimplemented!("{:?}", term.kind)
            }
        };

        self.apply_downcasts(&mut state, location)?;

        if let Some(state_expr) = state.expr_mut() {
            let mut expr = mem::replace(state_expr, true.into());
            expr = expr.set_default_pos(
                self.encoder
                    .error_manager()
                    .register_span(self.caller_def_id, span),
            );
            let _ = mem::replace(state_expr, expr);
        }

        Ok(state)
    }

    fn apply_statement(
        &self,
        bb: mir::BasicBlock,
        stmt_index: usize,
        stmt: &mir::Statement<'tcx>,
        state: &mut Self::State,
    ) -> Result<(), Self::Error> {
        trace!("apply_statement {:?}, state: {}", stmt, state);
        let span = stmt.source_info.span;
        let location = mir::Location {
            block: bb,
            statement_index: stmt_index,
        };

        match stmt.kind {
            mir::StatementKind::StorageLive(..)
            | mir::StatementKind::StorageDead(..)
            | mir::StatementKind::FakeRead(..)    // FIXME
            // | mir::StatementKind::ReadForMatch(..)
            // | mir::StatementKind::EndRegion(..)
            | mir::StatementKind::AscribeUserType(..)
             => {
                // Nothing to do
            }

            mir::StatementKind::Assign(box (lhs, ref rhs)) => {
                let (encoded_lhs, ty, _) = self.encode_place(lhs).unwrap();
                trace!("Encoding assignment to LHS {:?}", encoded_lhs);

                if !state.uses_place(&encoded_lhs) {
                    // If the lhs is not mentioned in our state, do nothing
                    trace!("The state does not mention {:?}", encoded_lhs);
                    return Ok(());
                }

                // The "is value"/"is not value" distinction should disappear as soon as
                // pure expressions use snapshots (= values) only.
                let can_lhs_be_value = match ty.kind() {
                    ty::TyKind::Bool
                    | ty::TyKind::Int(..)
                    | ty::TyKind::Uint(..)
                    | ty::TyKind::Float(..)
                    | ty::TyKind::RawPtr(..)
                    | ty::TyKind::Ref(..) => true,
                    ty::TyKind::Tuple(substs) if substs.is_empty() => true,
                    _ => false
                };
                let opt_lhs_value_place = if can_lhs_be_value {
                    Some(
                        self.encoder.encode_value_expr(
                            encoded_lhs.clone(),
                            ty
                        ).with_span(span)?
                        // encoded_lhs
                        //     .clone()
                        //     .field(self.encoder.encode_value_field(ty)),
                    )
                } else {
                    None
                };

                match rhs {
                    mir::Rvalue::Use(ref operand) => {
                        let (encoded_rhs, is_value) = self.encode_operand(operand).with_span(span)?;
                        if is_value {
                            if let Some(lhs_value_place) = &opt_lhs_value_place {
                                state.substitute_value(lhs_value_place, encoded_rhs);
                            }
                        } else {
                            state.substitute_value(&encoded_lhs, encoded_rhs);
                        }
                    }

                    mir::Rvalue::Aggregate(ref aggregate, ref operands) => {
                        debug!("Encode aggregate {:?}, {:?}", aggregate, operands);
                        match aggregate.as_ref() {
                            &mir::AggregateKind::Tuple => {
                                let field_types = if let ty::TyKind::Tuple(ref x) = ty.kind() {
                                    x
                                } else {
                                    unreachable!()
                                };
                                let mut field_exprs = vec![];
                                for (field_num, operand) in operands.iter().enumerate() {
                                    let field_name = format!("tuple_{}", field_num);
                                    let field_ty = field_types[field_num];
                                    let encoded_field = self.encoder
                                        .encode_raw_ref_field(field_name, field_ty)
                                        .with_span(span)?;
                                    let field_place = encoded_lhs.clone().field(encoded_field);

                                    let (encoded_rhs, is_value) = self.encode_operand(operand).with_span(span)?;
                                    if is_value {
                                        state.substitute_value(
                                            &self.encoder.encode_value_expr(field_place, field_ty)
                                                .with_span(span)?,
                                            encoded_rhs.clone(),
                                        );
                                    } else {
                                        state.substitute_value(&field_place, encoded_rhs.clone());
                                    }
                                    field_exprs.push(encoded_rhs);
                                }
                                let snapshot = self.encoder.encode_snapshot(
                                    ty,
                                    None,
                                    field_exprs,
                                ).with_span(span)?;
                                state.substitute_value(&encoded_lhs, snapshot);
                            }

                            &mir::AggregateKind::Adt(adt_did, variant_index, subst, _, _) => {
                                let tcx = self.encoder.env().tcx();
                                let adt_def = tcx.adt_def(adt_did);
                                let num_variants = adt_def.variants().len();
                                let variant_def = &adt_def.variants()[variant_index];
                                let mut encoded_lhs_variant = encoded_lhs.clone();
                                if num_variants > 1 {
                                    let discr_field = self.encoder.encode_discriminant_field();
                                    state.substitute_value(
                                        &encoded_lhs.clone().field(discr_field),
                                        variant_index.index().into(),
                                    );
                                    encoded_lhs_variant =
                                        encoded_lhs_variant.variant(variant_def.ident(tcx).as_str());
                                }
                                let mut field_exprs = vec![];
                                for (field_index, field) in variant_def.fields.iter().enumerate() {
                                    let operand = &operands[field_index];
                                    let field_name = field.ident(tcx).to_string();
                                    let field_ty = field.ty(tcx, subst);
                                    let encoded_field = self.encoder
                                        .encode_struct_field(&field_name, field_ty)
                                        .with_span(span)?;

                                    let field_place =
                                        encoded_lhs_variant.clone().field(encoded_field);

                                    let (encoded_rhs, is_value) = self.encode_operand(operand)
                                        .with_span(span)?;
                                    if is_value {
                                        state.substitute_value(
                                            &self.encoder.encode_value_expr(field_place, field_ty)
                                                .with_span(span)?,
                                            encoded_rhs.clone(),
                                        );
                                    } else {
                                        state.substitute_value(&field_place, encoded_rhs.clone());
                                    }
                                    field_exprs.push(encoded_rhs);
                                }
                                let snapshot = self.encoder.encode_snapshot(
                                    ty,
                                    Some(variant_index.as_usize()),
                                    field_exprs,
                                ).with_span(span)?;
                                state.substitute_value(&encoded_lhs, snapshot);
                            }

                            // TODO: clean up (duplication with Adt case)
                            &mir::AggregateKind::Closure(_def_id, substs) => {
                                let cl_substs = substs.as_closure();
                                let mut field_exprs = vec![];
                                for (field_index, field_ty) in cl_substs.upvar_tys().enumerate() {
                                    let operand = &operands[field_index];
                                    let field_name = format!("closure_{}", field_index);

                                    let encoded_field = self.encoder
                                        .encode_raw_ref_field(field_name, field_ty)
                                        .with_span(span)?;

                                    let field_place = encoded_lhs.clone()
                                        .field(encoded_field);

                                    let (encoded_rhs, is_value) = self.encode_operand(operand)
                                        .with_span(span)?;
                                    if is_value {
                                        state.substitute_value(
                                            &self.encoder.encode_value_expr(field_place, field_ty)
                                                .with_span(span)?,
                                            encoded_rhs.clone(),
                                        );
                                    } else {
                                        state.substitute_value(&field_place, encoded_rhs.clone());
                                    }
                                    field_exprs.push(encoded_rhs);
                                }
                                let snapshot = self.encoder.encode_snapshot(
                                    ty,
                                    None,
                                    field_exprs,
                                ).with_span(span)?;
                                state.substitute_value(&encoded_lhs, snapshot);
                            }

                            &mir::AggregateKind::Array(elem_ty) => {
                                let mut encoded_operands = Vec::with_capacity(operands.len());
                                for operand in operands {
                                    let (encoded_oper, _) = self.encode_operand(operand)
                                        .with_span(span)?;
                                    encoded_operands.push(encoded_oper);
                                }

                                let encoded_elem_ty = self.encoder.encode_snapshot_type(elem_ty)
                                    .with_span(span)?;
                                let elems = vir::Expr::Seq( vir::Seq {
                                    typ: vir::Type::Seq( vir::SeqType {typ: box encoded_elem_ty} ),
                                    elements: encoded_operands,
                                    position: vir::Position::default(),
                                });

                                let snapshot = self.encoder.encode_snapshot(
                                    ty,
                                    None,
                                    vec![elems],
                                ).with_span(span)?;

                                state.substitute_value(&encoded_lhs, snapshot);
                            }

                            ref x => unimplemented!("{:?}", x),
                        }
                    }

                    &mir::Rvalue::BinaryOp(op, box(ref left, ref right)) => {
                        let encoded_left = self.mir_encoder.encode_operand_expr(left)
                            .with_span(span)?;
                        let encoded_right = self.mir_encoder.encode_operand_expr(right)
                            .with_span(span)?;
                        let encoded_value = self.mir_encoder.encode_bin_op_expr(
                            op,
                            vir::Expr::snap_app(encoded_left),
                            vir::Expr::snap_app(encoded_right),
                            ty,
                        ).with_span(span)?;

                        // Substitute a place of a value with an expression
                        state.substitute_value(&opt_lhs_value_place.unwrap(), encoded_value);
                    }

                    &mir::Rvalue::CheckedBinaryOp(op, box (ref left, ref right)) => {
                        let operand_ty = if let ty::TyKind::Tuple(types) = ty.kind() {
                            types[0]
                        } else {
                            unreachable!()
                        };

                        let encoded_left = self.mir_encoder.encode_operand_expr(left)
                            .with_span(span)?;
                        let encoded_right = self.mir_encoder.encode_operand_expr(right)
                            .with_span(span)?;

                        let encoded_value = self.mir_encoder.encode_bin_op_expr(
                            op,
                            vir::Expr::snap_app(encoded_left.clone()),
                            vir::Expr::snap_app(encoded_right.clone()),
                            operand_ty,
                        ).with_span(span)?;
                        let encoded_check = self.mir_encoder.encode_bin_op_check(
                            op,
                            vir::Expr::snap_app(encoded_left),
                            vir::Expr::snap_app(encoded_right),
                            operand_ty,
                        ).with_span(span)?;

                        let field_types = if let ty::TyKind::Tuple(ref x) = ty.kind() {
                            x
                        } else {
                            unreachable!()
                        };
                        let value_field = self.encoder
                            .encode_raw_ref_field("tuple_0".to_string(), field_types[0])
                            .with_span(span)?;
                        let check_field = self.encoder
                            .encode_raw_ref_field("tuple_1".to_string(), field_types[1])
                            .with_span(span)?;

                        let lhs_value = encoded_lhs
                            .clone()
                            .field(value_field);
                        let lhs_check = encoded_lhs
                            .clone()
                            .field(check_field);

                        // Substitute a place of a value with an expression
                        state.substitute_value(&lhs_value, encoded_value);
                        state.substitute_value(&lhs_check, encoded_check);
                    }

                    &mir::Rvalue::UnaryOp(op, ref operand) => {
                        let encoded_val = self.mir_encoder.encode_operand_expr(operand)
                            .with_span(span)?;
                        let encoded_value = self.mir_encoder.encode_unary_op_expr(op, encoded_val);

                        // Substitute a place of a value with an expression
                        state.substitute_value(&opt_lhs_value_place.unwrap(), encoded_value);
                    }

                    mir::Rvalue::NullaryOp(_op, _op_ty) => unimplemented!(),

                    &mir::Rvalue::Discriminant(src) => {
                        let (encoded_src, src_ty, _) = self.encode_place(src).with_span(span)?;
                        match src_ty.kind() {
                            ty::TyKind::Adt(adt_def, _) if !adt_def.is_box() => {
                                let num_variants = adt_def.variants().len();

                                let discr_value: vir::Expr = if num_variants == 0 {
                                    let pos = self
                                        .encoder
                                        .error_manager()
                                        .register_error(stmt.source_info.span, ErrorCtxt::Unexpected, self.caller_def_id);
                                    let (function_name, type_arguments) = self.encoder.encode_builtin_function_use(
                                        BuiltinFunctionKind::Unreachable(vir::Type::Int),
                                    );
                                    vir::Expr::func_app(
                                        function_name,
                                        type_arguments,
                                        vec![],
                                        vec![],
                                        vir::Type::Int,
                                        pos,
                                    )
                                } else if num_variants == 1 {
                                    0u32.into()
                                } else {
                                    let discr_field = self.encoder.encode_discriminant_field();
                                    encoded_src.field(discr_field)
                                };

                                // Substitute a place of a value with an expression
                                state.substitute_value(&opt_lhs_value_place.unwrap(), discr_value);
                            }
                            ref x => {
                                panic!("The discriminant of type {:?} is not defined", x);
                            }
                        }
                    }

                    &mir::Rvalue::Ref(_, mir::BorrowKind::Unique, place)
                    | &mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place)
                    | &mir::Rvalue::Ref(_, mir::BorrowKind::Shared, place) => {
                        let (encoded_place, _, _) = self.encode_place(place).with_span(span)?;
                        // TODO: Instead of generating an `AddrOf(..)` expression, here we could
                        // generate a shapshot representing a reference. If we do so, we should
                        // also migrate the simplification done by `Expr::simplify_addr_of` to
                        // snapshots.
                        let encoded_ref = match encoded_place {
                            vir::Expr::Field( vir::FieldExpr {
                                box ref base,
                                field: vir::Field { ref name, .. },
                                ..
                            }) if name == "val_ref" => {
                                // Simplify "address of reference"
                                base.clone()
                            }
                            other_place => other_place.addr_of(),
                        };

                        // Substitute the place
                        state.substitute_value(&encoded_lhs, encoded_ref);
                    }

                    mir::Rvalue::Cast(mir::CastKind::Misc, ref operand, dst_ty) => {
                        let encoded_val = self.mir_encoder
                            .encode_cast_expr(operand, *dst_ty, span)?;

                        // Substitute a place of a value with an expression
                        state.substitute_value(&encoded_lhs, encoded_val);
                    }

                    &mir::Rvalue::Len(place) => {
                        let place_ty = self.encode_place(place).with_span(span)?.1;
                        match place_ty.kind() {
                            ty::TyKind::Array(..) => {
                                let array_types = self.encoder.encode_sequence_types(place_ty).with_span(span)?;
                                state.substitute_value(&opt_lhs_value_place.unwrap(), array_types.sequence_len.unwrap().into());
                            }
                            ty::TyKind::Slice(..) => {
                                let snap_len = self.encoder.encode_snapshot_slice_len(
                                    place_ty,
                                    self.encode_place(place).with_span(span)?.0,
                                ).with_span(span)?;

                                state.substitute_value(&opt_lhs_value_place.unwrap(), snap_len);
                            }
                            _ => span_bug!(span, "length should only be requested on arrays or slices"),
                        }
                    }

                    mir::Rvalue::Cast(mir::CastKind::Pointer(ty::adjustment::PointerCast::Unsize), ref operand, lhs_ref_ty) => {
                        let rhs_ref_ty = self.mir_encoder.get_operand_ty(operand);
                        if lhs_ref_ty.is_slice_ref() && rhs_ref_ty.is_array_ref() {
                            let lhs_ty = lhs_ref_ty.peel_refs();
                            let rhs_ty = rhs_ref_ty.peel_refs();
                            let function_name = self.encoder.encode_unsize_function_use(rhs_ty, lhs_ty)
                                .unwrap_or_else(|error| unreachable!("error during unsizing array to slice: {:?}", error) );
                            let encoded_rhs = self.encoder.encode_snapshot_type(rhs_ty).with_span(span)?;
                            let formal_args = vec![vir::LocalVar::new(
                                String::from("array"),
                                encoded_rhs,
                            )];
                            let encoded_arg = self.encoder.encode_value_expr(self.encode_operand(operand).with_span(span)?.0, rhs_ref_ty).with_span(span)?;
                            let unsize_func = vir::Expr::func_app(
                                function_name,
                                Vec::new(),     // FIXME: This is probably wrong.
                                vec![encoded_arg],
                                formal_args,
                                self.encoder.encode_snapshot_type(lhs_ty).with_span(span)?,
                                vir::Position::default(),
                            );
                            state.substitute_value(&opt_lhs_value_place.unwrap(), unsize_func);
                        } else {
                            return Err(SpannedEncodingError::unsupported(
                                format!("unsizing a {} into a {} is not supported", rhs_ref_ty, lhs_ref_ty),
                                span,
                            ));
                        }
                    }

                    mir::Rvalue::Repeat(ref operand, times) => {
                        let (encoded_operand, _) = self.encode_operand(operand).with_span(span)?;
                        let len: usize = self.encoder.const_eval_intlike(mir::ConstantKind::Ty(*times)).with_span(span)?
                            .to_u64().unwrap().try_into().unwrap();
                        let elem_ty = operand.ty(self.mir, self.encoder.env().tcx());
                        let encoded_elem_ty = self.encoder.encode_snapshot_type(elem_ty)
                            .with_span(span)?;
                        let elems = vir::Expr::Seq(vir::Seq {
                            typ: vir::Type::Seq(vir::SeqType{ typ: box encoded_elem_ty }),
                            elements: (0..len).map(|_| encoded_operand.clone()).collect(),
                            position: vir::Position::default(),
                        });

                        let snapshot = self.encoder.encode_snapshot(
                            ty,
                            None,
                            vec![elems],
                        ).with_span(span)?;

                        state.substitute_value(&encoded_lhs, snapshot);
                    }

                    ref rhs => {
                        unimplemented!("encoding of '{:?}'", rhs);
                    }
                }
            }

            ref stmt => unimplemented!("encoding of '{:?}'", stmt),
        }

        self.apply_downcasts(state, location)?;

        if let Some(state_expr) = state.expr_mut() {
            let mut expr = mem::replace(state_expr, true.into());
            expr = expr.set_default_pos(self.encoder.error_manager().register_error(
                span,
                ErrorCtxt::PureFunctionDefinition,
                self.caller_def_id,
            ));
            let _ = mem::replace(state_expr, expr);
        }

        Ok(())
    }
}
