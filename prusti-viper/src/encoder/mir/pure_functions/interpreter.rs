use super::{super::super::encoder::SubstMap, interface::PureFunctionEncoderInterface};
use crate::encoder::{
    borrows::{compute_procedure_contract, ProcedureContract},
    builtin_encoder::BuiltinFunctionKind,
    errors::{
        EncodingError, EncodingResult, ErrorCtxt, PanicCause, SpannedEncodingError,
        SpannedEncodingResult, WithSpan,
    },
    foldunfold,
    high::types::HighTypeEncoderInterface,
    mir::types::MirTypeEncoderInterface,
    mir_encoder::{MirEncoder, PlaceEncoder, PlaceEncoding, PRECONDITION_LABEL, WAND_LHS_LABEL},
    mir_interpreter::{
        run_backward_interpretation, BackwardMirInterpreter, ExprBackwardInterpreterState,
    },
    snapshot, Encoder,
};
use log::{debug, trace};
use prusti_common::{config, vir::optimizations::functions::Simplifier, vir_local};
use prusti_interface::{specs::typed, PrustiError};
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, span_bug, ty};
use rustc_span::Span;
use std::{collections::HashMap, mem};
use vir_crate::polymorphic::{self as vir, ExprIterator};

pub(crate) struct PureFunctionBackwardInterpreter<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    /// MIR of the pure function being encoded.
    mir: &'p mir::Body<'tcx>,
    /// MirEncoder of the pure function being encoded.
    mir_encoder: MirEncoder<'p, 'v, 'tcx>,
    /// True if a panic should be encoded to a `false` boolean value.
    /// This flag is used to distinguish whether an assert terminators generated e.g. for an
    /// integer overflow should be translated into `false` and when to an "unreachable" function
    /// call with a `false` precondition.
    encode_panic_to_false: bool,
    /// DefId of the caller. Used for error reporting.
    caller_def_id: DefId,
    tymap: SubstMap<'tcx>,
}

/// This encoding works backward, so there is the risk of generating expressions whose length
/// is exponential in the number of branches. If this becomes a problem, consider doing a forward
/// encoding (keeping path conditions expressions).
impl<'p, 'v: 'p, 'tcx: 'v> PureFunctionBackwardInterpreter<'p, 'v, 'tcx> {
    pub(crate) fn new(
        encoder: &'p Encoder<'v, 'tcx>,
        mir: &'p mir::Body<'tcx>,
        def_id: DefId,
        encode_panic_to_false: bool,
        caller_def_id: DefId,
        tymap: SubstMap<'tcx>,
    ) -> Self {
        PureFunctionBackwardInterpreter {
            encoder,
            mir,
            mir_encoder: MirEncoder::new(encoder, mir, def_id),
            encode_panic_to_false,
            caller_def_id,
            tymap,
        }
    }

    pub(crate) fn mir_encoder(&self) -> &MirEncoder<'p, 'v, 'tcx> {
        &self.mir_encoder
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
                    let variant_name = &adt_def.variants[variant_idx].ident.as_str();
                    self.encoder.encode_enum_variant_field(variant_name)
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

    fn encode_place(
        &self,
        place: &mir::Place<'tcx>,
    ) -> EncodingResult<(vir::Expr, ty::Ty<'tcx>, Option<usize>)> {
        let (encoded_place, ty, variant_idx) = self.mir_encoder().encode_place(place)?;
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

    fn encode_operand_place(
        &self,
        operand: &mir::Operand<'tcx>,
    ) -> EncodingResult<Option<vir::Expr>> {
        // TODO: De-duplicate with mir_encoder.encode_operand_place.
        //   Maybe returning `None` from mir_encoder.encode_operand_place for arrays in general?
        Ok(match operand {
            mir::Operand::Move(ref place) | &mir::Operand::Copy(ref place) => {
                Some(self.encode_place(place)?.0)
            }

            mir::Operand::Constant(_) => None,
        })
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
                let idx_val_int = self
                    .encoder
                    .patch_snapshots(vir::Expr::snap_app(index), &self.tymap)?;

                self.encoder.encode_snapshot_array_idx(
                    rust_array_ty,
                    postprocessed_base,
                    idx_val_int,
                    &self.tymap,
                )?
            }
            PlaceEncoding::SliceAccess {
                box base,
                index,
                rust_slice_ty,
                ..
            } => {
                let postprocessed_base = self.postprocess_place_encoding(base)?;
                let idx_val_int = self
                    .encoder
                    .patch_snapshots(vir::Expr::snap_app(index), &self.tymap)?;

                self.encoder.encode_snapshot_slice_idx(
                    rust_slice_ty,
                    postprocessed_base,
                    idx_val_int,
                    &self.tymap,
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
        states: HashMap<mir::BasicBlock, &Self::State>,
    ) -> Result<Self::State, Self::Error> {
        trace!("apply_terminator {:?}, states: {:?}", term, states);
        use rustc_middle::mir::TerminatorKind;
        let span = term.source_info.span;
        let location = self.mir.terminator_loc(bb);

        // Generate a function call that leaves the expression undefined.
        let unreachable_expr =
            |pos| {
                self.encoder
                    .encode_snapshot_type(self.mir.return_ty(), &self.tymap)
                    .map(|encoded_type| {
                        let function_name = self.encoder.encode_builtin_function_use(
                            BuiltinFunctionKind::Unreachable(encoded_type.clone()),
                        );
                        vir::Expr::func_app(function_name, vec![], vec![], encoded_type, pos)
                    })
            };

        // Generate a function call that leaves the expression undefined.
        let undef_expr =
            |pos| {
                self.encoder
                    .encode_snapshot_type(self.mir.return_ty(), &self.tymap)
                    .map(|encoded_type| {
                        let function_name = self.encoder.encode_builtin_function_use(
                            BuiltinFunctionKind::Undefined(encoded_type.clone()),
                        );
                        vir::Expr::func_app(function_name, vec![], vec![], encoded_type, pos)
                    })
            };

        let mut state = match term.kind {
            TerminatorKind::Unreachable => {
                assert!(states.is_empty());
                let pos = self.encoder.error_manager().register(
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
                let pos = self.encoder.error_manager().register(
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

                let final_expr = states[&refined_default_target].expr().map(|default_expr| {
                    cfg_targets
                        .iter()
                        .map(|(guard, target)|
                            // If the default target is defined, all targets should be defined.
                            (guard, states[target].expr().unwrap()))
                        .fold(default_expr.clone(), |else_expr, (guard, then_expr)| {
                            if then_expr == &else_expr {
                                // Optimization
                                else_expr
                            } else {
                                vir::Expr::ite(guard.clone(), then_expr.clone(), else_expr)
                            }
                        })
                });
                ExprBackwardInterpreterState::new(final_expr)
            }

            TerminatorKind::DropAndReplace { .. } => unimplemented!(),

            TerminatorKind::Call {
                ref args,
                ref destination,
                func:
                    mir::Operand::Constant(box mir::Constant {
                        literal: mir::ConstantKind::Ty(ty::Const { ty, val: _ }),
                        ..
                    }),
                ..
            } => {
                if let ty::TyKind::FnDef(def_id, substs) = ty.kind() {
                    let def_id = *def_id;
                    let full_func_proc_name: &str = &self.encoder.env().tcx().def_path_str(def_id);
                    // &self.encoder.env().tcx().absolute_item_path_str(def_id);
                    let func_proc_name = &self.encoder.env().get_item_name(def_id);

                    let own_substs = ty::List::identity_for_item(self.encoder.env().tcx(), def_id);

                    // FIXME: this is a hack to support generics. See issue #187.
                    let mut new_tymap = HashMap::new();
                    for (kind1, kind2) in own_substs.iter().zip(substs.iter()) {
                        if let (
                            ty::subst::GenericArgKind::Type(ty1),
                            ty::subst::GenericArgKind::Type(ty2),
                        ) = (kind1.unpack(), kind2.unpack())
                        {
                            new_tymap.insert(ty1, ty2);
                        }
                    }
                    // let _cleanup_token = self.encoder.push_temp_tymap(tymap);
                    let subst_stack = vec![self.tymap.clone(), new_tymap];
                    let tymap = self.encoder.merge_tymaps(subst_stack);

                    let state = if destination.is_some() {
                        let (ref lhs_place, target_block) = destination.as_ref().unwrap();
                        let (encoded_lhs, ty, _) = self.encode_place(lhs_place).with_span(span)?;
                        let lhs_value = self
                            .encoder
                            .encode_value_expr(encoded_lhs.clone(), ty)
                            .with_span(span)?;
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
                                let mut state = states[target_block].clone();
                                state.substitute_value(&encoded_lhs, encoded_rhs);
                                state
                            }

                            "prusti_contracts::before_expiry" => {
                                trace!("Encoding before_expiry expression {:?}", args[0]);
                                assert_eq!(args.len(), 1);
                                let encoded_rhs = self
                                    .mir_encoder
                                    .encode_old_expr(encoded_args[0].clone(), WAND_LHS_LABEL);
                                let mut state = states[target_block].clone();
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
                                let mut state = states[target_block].clone();
                                state.substitute_value(&lhs_value, encoded_rhs);
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
                                let mut state = states[target_block].clone();
                                state.substitute_value(&lhs_value, encoded_rhs);
                                state
                            }

                            "core::slice::<impl [T]>::len" => {
                                assert_eq!(args.len(), 1);
                                let slice_ty = self.mir_encoder.get_operand_ty(&args[0]);
                                let len = self
                                    .encoder
                                    .encode_snapshot_slice_len(
                                        slice_ty,
                                        encoded_args[0].clone(),
                                        &self.tymap,
                                    )
                                    .with_span(span)?;

                                let mut state = states[target_block].clone();
                                state.substitute_value(&lhs_value, len);
                                state
                            }

                            "std::ops::Index::index" | "core::ops::Index::index" => {
                                assert_eq!(args.len(), 2);
                                trace!("slice::index(args={:?}, encoded_args={:?}, ty={:?}, lhs_value={:?})", args, encoded_args, ty, lhs_value);

                                let base_ty = self.mir_encoder.get_operand_ty(&args[0]);

                                let idx_ty = self.mir_encoder.get_operand_ty(&args[1]);
                                let idx_ty_did = match idx_ty.ty_adt_def() {
                                    Some(def) => def.did,
                                    None => return Err(SpannedEncodingError::unsupported(
                                        format!("Using {} as index/range type for {} is not currently supported in pure functions", idx_ty, base_ty),
                                        span,
                                    ))
                                };
                                let idx_ident = self.encoder.env().tcx().def_path_str(idx_ty_did);
                                let encoded_idx = &encoded_args[1];

                                let (start, end) = match &*idx_ident {
                                    "std::ops::Range"
                                    | "core::ops::Range" => {
                                        // there's fields like _5.f$start.val_int on `encoded_idx`, it just feels hacky to
                                        // manually re-do them here when we probably just encoded the type and the
                                        // construction of the fields..
                                        let usize_ty = self.encoder.env().tcx().mk_ty(ty::TyKind::Uint(ty::UintTy::Usize));
                                        let start = encoded_idx.clone()
                                            .field(self.encoder.encode_struct_field("start", usize_ty).with_span(span)?);
                                        let start_expr = self.encoder.encode_value_expr(start, usize_ty).with_span(span)?;

                                        let end = encoded_idx.clone()
                                            .field(self.encoder.encode_struct_field("end", usize_ty).with_span(span)?);
                                        let end_expr = self.encoder.encode_value_expr(end, usize_ty).with_span(span)?;

                                        (start_expr, end_expr)
                                    },
                                    // other things like RangeFull, RangeFrom, RangeTo, RangeInclusive could be added here
                                    // relatively easily
                                    _ => return Err(SpannedEncodingError::unsupported(
                                        format!("slicing with {} as index/range type is not supported yet", idx_ident),
                                        span,
                                    )),
                                };

                                let slice_expr = self
                                    .encoder
                                    .encode_snapshot_slicing(
                                        base_ty,
                                        encoded_args[0].clone(),
                                        ty,
                                        start,
                                        end,
                                        &self.tymap,
                                    )
                                    .with_span(span)?;

                                let mut state = states[target_block].clone();
                                state.substitute_value(&lhs_value, slice_expr);
                                state
                            }

                            // simple function call
                            _ => {
                                let is_pure_function = self.encoder.is_pure(def_id);
                                let (function_name, return_type) = if is_pure_function {
                                    self.encoder
                                        .encode_pure_function_use(
                                            def_id,
                                            self.caller_def_id,
                                            &tymap,
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
                                            .encode_operand_expr_type(arg, &self.tymap)
                                            .map(|ty| vir::LocalVar::new(format!("x{}", i), ty))
                                    })
                                    .collect::<Result<_, _>>()
                                    .with_span(term.source_info.span)?;

                                let pos = self.encoder.error_manager().register(
                                    term.source_info.span,
                                    ErrorCtxt::PureFunctionCall,
                                    self.caller_def_id,
                                );
                                let encoded_rhs = vir::Expr::func_app(
                                    function_name,
                                    encoded_args,
                                    formal_args,
                                    return_type,
                                    pos,
                                );
                                let mut state = states[target_block].clone();
                                state.substitute_value(&lhs_value, encoded_rhs);
                                state
                            }
                        }
                    } else {
                        // FIXME: Refactor the common code with the procedure encoder.

                        // Encoding of a non-terminating function call
                        let error_ctxt = match full_func_proc_name {
                            "std::rt::begin_panic"
                            | "core::panicking::panic"
                            | "core::panicking::panic_fmt" => {
                                // This is called when a Rust assertion fails
                                // args[0]: message
                                // args[1]: position of failing assertions

                                let panic_cause =
                                    self.mir_encoder.encode_panic_cause(term.source_info);
                                ErrorCtxt::PanicInPureFunction(panic_cause)
                            }

                            _ => ErrorCtxt::DivergingCallInPureFunction,
                        };
                        let pos = self.encoder.error_manager().register(
                            term.source_info.span,
                            error_ctxt,
                            self.caller_def_id,
                        );
                        ExprBackwardInterpreterState::new_defined(
                            unreachable_expr(pos).with_span(term.source_info.span)?,
                        )
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

                let pos = self.encoder.error_manager().register(
                    term.source_info.span,
                    error_ctxt,
                    self.caller_def_id,
                );

                let failure_encoding = if self.encode_panic_to_false {
                    // We are encoding an assertion, so all failures should be equivalent to false.
                    debug_assert!(matches!(self.mir.return_ty().kind(), ty::TyKind::Bool));
                    false.into()
                } else {
                    // We are encoding a pure function, so all failures should be unreachable.
                    unreachable_expr(pos).with_span(term.source_info.span)?
                };

                ExprBackwardInterpreterState::new(states[target].expr().map(|target_expr| {
                    vir::Expr::ite(viper_guard.clone(), target_expr.clone(), failure_encoding)
                }))
            }

            TerminatorKind::Yield { .. }
            | TerminatorKind::GeneratorDrop
            | TerminatorKind::InlineAsm { .. } => {
                unimplemented!("{:?}", term.kind)
            }
        };

        self.apply_downcasts(&mut state, location)?;

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
             => {
                // Nothing to do
            }

            mir::StatementKind::Assign(box (ref lhs, ref rhs)) => {
                let (encoded_lhs, ty, _) = self.encode_place(lhs).unwrap();
                trace!("Encoding assignment to LHS {:?}", encoded_lhs);

                if !state.uses_place(&encoded_lhs) {
                    // If the lhs is not mentioned in our state, do nothing
                    trace!("The state does not mention {:?}", encoded_lhs);
                    return Ok(());
                }

                let opt_lhs_value_place = match ty.kind() {
                    ty::TyKind::Bool
                    | ty::TyKind::Int(..)
                    | ty::TyKind::Uint(..)
                    | ty::TyKind::RawPtr(..)
                    | ty::TyKind::Ref(..) => Some(
                        self.encoder.encode_value_expr(
                            encoded_lhs.clone(),
                            ty
                        ).with_span(span)?
                        // encoded_lhs
                        //     .clone()
                        //     .field(self.encoder.encode_value_field(ty)),
                    ),
                    _ => None,
                };

                match rhs {
                    &mir::Rvalue::Use(ref operand) => {
                        let opt_encoded_rhs = self.encode_operand_place(operand)
                            .with_span(span)?;

                        match opt_encoded_rhs {
                            Some(encoded_rhs) => {
                                // Substitute a place
                                state.substitute_value(&encoded_lhs, encoded_rhs);
                            }
                            None => {
                                // Substitute a place of a value with an expression
                                if let Some(lhs_value_place) = &opt_lhs_value_place {
                                    // opt_lhs_value_place can be none in trigger generation code.
                                    let rhs_expr = self.mir_encoder
                                        .encode_operand_expr(operand)
                                        .with_span(span)?;
                                    state.substitute_value(lhs_value_place, rhs_expr);
                                }
                            }
                        }
                    }

                    &mir::Rvalue::Aggregate(ref aggregate, ref operands) => {
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
                                        .encode_raw_ref_field(field_name, field_ty.expect_ty())
                                        .with_span(span)?;
                                    let field_place = encoded_lhs.clone().field(encoded_field);

                                    let encoded_operand = self.encode_operand_place(operand)
                                        .with_span(span)?;
                                    match encoded_operand {
                                        Some(encoded_rhs) => {
                                            // Substitute a place
                                            field_exprs.push(encoded_rhs.clone());
                                            state.substitute_value(&field_place, encoded_rhs);
                                        }
                                        None => {
                                            // Substitute a place of a value with an expression
                                            let rhs_expr =
                                                self.mir_encoder.encode_operand_expr(operand)
                                                    .with_span(span)?;
                                            field_exprs.push(rhs_expr.clone());
                                            state.substitute_value(
                                                &self.encoder.encode_value_expr(field_place, field_ty.expect_ty()).with_span(span)?,
                                                rhs_expr,
                                            );
                                        }
                                    }
                                }
                                let snapshot = self.encoder.encode_snapshot_constructor(
                                    ty,
                                    field_exprs,
                                    &self.tymap,
                                ).with_span(span)?;
                                state.substitute_value(&encoded_lhs, snapshot);
                            }

                            &mir::AggregateKind::Adt(adt_def, variant_index, subst, _, _) => {
                                let num_variants = adt_def.variants.len();
                                let variant_def = &adt_def.variants[variant_index];
                                let mut encoded_lhs_variant = encoded_lhs.clone();
                                if num_variants > 1 {
                                    let discr_field = self.encoder.encode_discriminant_field();
                                    state.substitute_value(
                                        &encoded_lhs.clone().field(discr_field),
                                        variant_index.index().into(),
                                    );
                                    encoded_lhs_variant =
                                        encoded_lhs_variant.variant(&variant_def.ident.as_str());
                                }
                                let mut field_exprs = vec![];
                                for (field_index, field) in variant_def.fields.iter().enumerate() {
                                    let operand = &operands[field_index];
                                    let field_name = &field.ident.as_str();
                                    let tcx = self.encoder.env().tcx();
                                    let field_ty = field.ty(tcx, subst);
                                    let encoded_field = self.encoder
                                            .encode_struct_field(field_name, field_ty)
                                            .with_span(span)?;

                                    let field_place =
                                        encoded_lhs_variant.clone().field(encoded_field);

                                    let encoded_operand = self.encode_operand_place(operand)
                                        .with_span(span)?;
                                    match encoded_operand {
                                        Some(encoded_rhs) => {
                                            // Substitute a place
                                            field_exprs.push(encoded_rhs.clone());
                                            state.substitute_value(&field_place, encoded_rhs);
                                        }
                                        None => {
                                            // Substitute a place of a value with an expression
                                            let rhs_expr =
                                                self.mir_encoder.encode_operand_expr(operand)
                                                    .with_span(span)?;
                                            field_exprs.push(rhs_expr.clone());
                                            state.substitute_value(
                                                &self.encoder.encode_value_expr(field_place, field_ty).with_span(span)?,
                                                rhs_expr,
                                            );
                                        }
                                    }
                                }
                                // TODO: construct snapshot for enumerations
                                if num_variants == 1 {
                                    let snapshot = self.encoder.encode_snapshot_constructor(
                                        ty,
                                        field_exprs,
                                        &self.tymap,
                                    ).with_span(span)?;
                                    state.substitute_value(&encoded_lhs, snapshot);
                                }
                            }

                            &mir::AggregateKind::Array(elem_ty) => {
                                let mut encoded_operands = Vec::with_capacity(operands.len());
                                for oper in operands {
                                    let encoded_oper = self.encode_operand_place(oper)
                                        .with_span(span)?;
                                    let encoded_oper = match encoded_oper {
                                        Some(encoded_rhs) => encoded_rhs,
                                        None => {
                                            self.mir_encoder.encode_operand_expr(oper)
                                                .with_span(span)?
                                        }
                                    };
                                    encoded_operands.push(encoded_oper);
                                }

                                let encoded_elem_ty = self.encoder.encode_snapshot_type(elem_ty, &self.tymap)
                                    .with_span(span)?;
                                let elems = vir::Expr::Seq( vir::Seq {
                                    typ: vir::Type::Seq( vir::SeqType {typ: box encoded_elem_ty} ),
                                    elements: encoded_operands,
                                    position: vir::Position::default(),
                                });

                                let snapshot = self.encoder.encode_snapshot_constructor(
                                    ty,
                                    vec![elems],
                                    &self.tymap,
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
                            operand_ty.expect_ty(),
                        ).with_span(span)?;
                        let encoded_check = self.mir_encoder.encode_bin_op_check(
                            op,
                            vir::Expr::snap_app(encoded_left),
                            vir::Expr::snap_app(encoded_right),
                            operand_ty.expect_ty(),
                        ).with_span(span)?;

                        let field_types = if let ty::TyKind::Tuple(ref x) = ty.kind() {
                            x
                        } else {
                            unreachable!()
                        };
                        let value_field = self.encoder
                            .encode_raw_ref_field("tuple_0".to_string(), field_types[0].expect_ty())
                            .with_span(span)?;
                        let value_field_value = self.encoder
                            .encode_value_field(field_types[0].expect_ty()).with_span(span)?;
                        let check_field = self.encoder
                            .encode_raw_ref_field("tuple_1".to_string(), field_types[1].expect_ty())
                            .with_span(span)?;
                        let check_field_value = self.encoder
                            .encode_value_field(field_types[1].expect_ty()).with_span(span)?;

                        let lhs_value = encoded_lhs
                            .clone()
                            .field(value_field)
                            .field(value_field_value);
                        let lhs_check = encoded_lhs
                            .clone()
                            .field(check_field)
                            .field(check_field_value);

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

                    &mir::Rvalue::NullaryOp(_op, _op_ty) => unimplemented!(),

                    &mir::Rvalue::Discriminant(ref src) => {
                        let (encoded_src, src_ty, _) = self.encode_place(src).with_span(span)?;
                        match src_ty.kind() {
                            ty::TyKind::Adt(adt_def, _) if !adt_def.is_box() => {
                                let num_variants = adt_def.variants.len();

                                let discr_value: vir::Expr = if num_variants == 0 {
                                    let pos = self
                                        .encoder
                                        .error_manager()
                                        .register(stmt.source_info.span, ErrorCtxt::Unexpected, self.caller_def_id);
                                    let function_name = self.encoder.encode_builtin_function_use(
                                        BuiltinFunctionKind::Unreachable(vir::Type::Int),
                                    );
                                    vir::Expr::func_app(
                                        function_name,
                                        vec![],
                                        vec![],
                                        vir::Type::Int,
                                        pos,
                                    )
                                } else if num_variants == 1 {
                                    0.into()
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

                    &mir::Rvalue::Ref(_, mir::BorrowKind::Unique, ref place)
                    | &mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, ref place)
                    | &mir::Rvalue::Ref(_, mir::BorrowKind::Shared, ref place) => {
                        let (encoded_place, _, _) = self.encode_place(place).with_span(span)?;
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

                    &mir::Rvalue::Cast(mir::CastKind::Misc, ref operand, dst_ty) => {
                        let encoded_val = self.mir_encoder
                            .encode_cast_expr(operand, dst_ty, stmt.source_info.span, &self.tymap)?;

                        // Substitute a place of a value with an expression
                        state.substitute_value(&opt_lhs_value_place.unwrap(), encoded_val);
                    }

                    &mir::Rvalue::Len(ref place) => {
                        let place_ty = self.encode_place(place).with_span(span)?.1;
                        match place_ty.kind() {
                            ty::TyKind::Array(..) => {
                                let array_types = self.encoder.encode_array_types(place_ty).with_span(span)?;
                                state.substitute_value(&opt_lhs_value_place.unwrap(), array_types.array_len.into());
                            }
                            ty::TyKind::Slice(..) => {
                                let snap_len = self.encoder.encode_snapshot_slice_len(
                                    place_ty,
                                    self.encode_place(place).with_span(span)?.0,
                                    &self.tymap,
                                ).with_span(span)?;

                                state.substitute_value(&opt_lhs_value_place.unwrap(), snap_len);
                            }
                            _ => span_bug!(span, "length should only be requested on arrays or slices"),
                        }
                    }

                    &mir::Rvalue::Cast(mir::CastKind::Pointer(ty::adjustment::PointerCast::Unsize), ref operand, ty) => {
                        if !ty.is_slice() {
                            return Err(EncodingError::unsupported(
                                "unsizing a pointer or reference value is not supported"
                            )).with_span(span);
                        }

                        let rhs_array_ref_ty = self.mir_encoder.get_operand_ty(operand);
                        let encoded_rhs = if let Some(encoded_place) = self.encode_operand_place(operand).with_span(span)? {
                            encoded_place
                        } else {
                            self.mir_encoder.encode_operand_expr(operand)
                                .with_span(span)?
                        };
                        // encoded_rhs is something like ref$Array$.. or ref$Slice$.. but we want .val_ref: Array$..
                        let encoded_rhs = self.encoder.encode_value_expr(encoded_rhs, rhs_array_ref_ty).with_span(span)?;
                        let rhs_array_ty = if let ty::TyKind::Ref(_, array_ty, _) = rhs_array_ref_ty.kind() {
                            array_ty
                        } else {
                            unreachable!("rhs array not a ref?")
                        };
                        trace!("rhs_array_ty: {:?}", rhs_array_ty);
                        let array_types = self.encoder.encode_array_types(rhs_array_ty).with_span(span)?;

                        let encoded_array_elems = (0..array_types.array_len)
                            .map(|idx| {
                                self.encoder.encode_snapshot_array_idx(rhs_array_ty, encoded_rhs.clone(), idx.into(),&self.tymap,)
                            })
                            .collect::<Result<Vec<_>, _>>()
                            .with_span(span)?;

                        let elem_snap_ty = self.encoder.encode_snapshot_type(array_types.elem_ty_rs, &self.tymap).with_span(span)?;
                        let elems_seq = vir::Expr::Seq( vir::Seq {
                            typ: vir::Type::Seq( vir::SeqType {typ: box elem_snap_ty} ),
                            elements: encoded_array_elems,
                            position: vir::Position::default(),
                        });

                        let slice_snap = self.encoder.encode_snapshot_constructor(ty, vec![elems_seq], &self.tymap,).with_span(span)?;

                        state.substitute_value(&opt_lhs_value_place.unwrap(), slice_snap);

                    }

                    ref rhs => {
                        unimplemented!("encoding of '{:?}'", rhs);
                    }
                }
            }

            ref stmt => unimplemented!("encoding of '{:?}'", stmt),
        }

        self.apply_downcasts(state, location)?;

        Ok(())
    }
}
