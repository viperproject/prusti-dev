use prusti_rustc_interface::{
    middle::{mir, ty},
    span::symbol,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn, MethodIdn};

use crate::encoders::{
    TyUseImpureEnc,
    builtin::{MetadataCastEnc, ValueCastEnc},
    ty::{
        LazyRustTy, RustTy, RustTyDecomposition, TySpecifics,
        generics::{GParams, GenericParamsEnc},
        use_pure::TyUsePureEnc,
    },
};

/// Encodes the builtin MIR cast operations (e.g. `IntToInt`, `PointerCoercion`)
/// as Viper functions with the correct semantics. The pointer coercion ones are
/// applied to generic refs (the inner type is a parameter) and thus the meaning
/// for those is given by axioms for concrete types (e.g. `&[T; N] -> &[T]`).
/// Also returns a side-effecting `unsize`/`undo` method for coercing the inner
/// referent (i.e. an `p_Param` to `p_Param` with different type).
///
/// Use `MirBuiltinUseCastEnc` to encode a cast in a specific context (with concrete
/// type arguments).
pub(super) struct MirBuiltinCastEnc;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub(super) struct MirBuiltinCastTask<'vir> {
    pub(super) result_ty: RustTy<'vir>,
    pub(super) kind: mir::CastKind,
    pub(super) operand_ty: RustTy<'vir>,
}

/// The result of encoding a builtin cast.
#[derive(Debug, Clone, Copy)]
pub(super) enum MirBuiltinCastOutput<'vir> {
    /// A pure value-level cast (e.g. integer-to-integer): a single function from
    /// the operand snapshot to the result snapshot.
    Simple(FunctionIdn<'vir, vir::CSnap, vir::CSnap>),
    /// An unsizing coercion (e.g. `&[T; N] -> &[T]`). `cast` builds the
    /// (wide-pointer) result snapshot from the operand snapshot. For `&mut`
    /// coercions the side-effecting `unsize`/`undo` methods transfer permission
    /// between the original and the coerced reference; they are `None` for
    /// shared references (and currently for all coercions, pending completion).
    Unsize {
        cast: FunctionIdn<'vir, (vir::CSnap, vir::ManyTyVal, vir::ManyCSnap), vir::CSnap>,
        unsize: Option<vir::MethodIdn<'vir, (vir::CSnap, vir::ManyTyVal, vir::ManyCSnap)>>,
        undo: Option<vir::MethodIdn<'vir, (vir::CSnap, vir::ManyTyVal, vir::ManyCSnap)>>,
    },
}

/// The Viper definitions produced for a builtin cast: always the cast function,
/// plus the side-effecting `unsize`/`undo` methods for `&mut` unsize coercions.
#[derive(Debug, Clone, Copy)]
pub(super) struct MirBuiltinCastLocal<'vir> {
    cast: vir::Function<'vir>,
    unsize: Option<vir::Method<'vir>>,
    undo: Option<vir::Method<'vir>>,
}

impl TaskEncoder for MirBuiltinCastEnc {
    task_encoder::encoder_cache!(MirBuiltinCastEnc);
    const ENCODER_NAME: &'static str = "MIR builtin cast encoder";

    type TaskDescription<'vir> = MirBuiltinCastTask<'vir>;

    type OutputFullDependency<'vir> = MirBuiltinCastOutput<'vir>;
    type OutputFullLocal<'vir> = MirBuiltinCastLocal<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let MirBuiltinCastTask {
            result_ty,
            kind,
            operand_ty,
        } = *task_key;
        let op_ty = RustTyDecomposition::identity(operand_ty);
        let op_ty = deps.require_dep::<TyUsePureEnc>(op_ty)?;
        let op_ty_snap = op_ty.snapshot.downcast_ty::<vir::CSnap>();
        let res_ty = RustTyDecomposition::identity(result_ty);
        let res_ty = deps.require_dep::<TyUsePureEnc>(res_ty)?;
        let res_ty_snap = res_ty.snapshot.downcast_ty::<vir::CSnap>();

        let name = match kind {
            mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, ..) => "unsize",
            mir::CastKind::IntToInt => "i2i",
            mir::CastKind::PtrToPtr => "p2p",
            other => todo!("cast kind {other:?}"),
        };
        // The unsize cast/methods don't depend on the pointee type (the methods
        // are generic over the input/output referent type values), so the name
        // only uses the reference types and the task deduplicates across pointees.
        let name = vir::with_vcx(|vcx| {
            vir::vir_format_identifier!(
                vcx,
                "mir_cast_{name}_{}_to_{}",
                operand_ty.name(),
                result_ty.name(),
            )
        });
        vir::with_vcx(|vcx| {
            let arg_decl = vcx.mk_local_decl("arg", op_ty_snap);
            let arg_ex = vcx.mk_local_ex(arg_decl);
            let output = match kind {
                mir::CastKind::IntToInt => {
                    let e_op_ty = op_ty.expect_primitive();
                    let e_res_ty = res_ty.expect_primitive();
                    let result_kind = result_ty.expect_primitive().kind();
                    let operand_kind = operand_ty.expect_primitive().kind();

                    // An integer `as` cast never panics: when every value of the
                    // source type is representable in the target the value is
                    // preserved unchanged; otherwise it is truncated to the target
                    // width and reinterpreted with the target's signedness. Either
                    // way any input is valid, so the cast function needs NO
                    // precondition.
                    let wrapped = if matches!(operand_kind, ty::TyKind::Bool) {
                        // `bool as <int>` is `b ? 1 : 0`; always lossless.
                        vcx.mk_ternary_expr(
                            arg_ex.downcast_ty(),
                            vcx.mk_int::<1>(),
                            vcx.mk_int::<0>(),
                        )
                        .upcast_ty()
                    } else {
                        let (to_bits, to_signed) = vir::VirCtxt::get_int_data(result_kind);
                        let (from_bits, from_signed) = vir::VirCtxt::get_int_data(operand_kind);

                        let arg_prim = e_op_ty.snap_to_prim(arg_ex);

                        let lossless = match (from_signed, to_signed) {
                            (false, false) | (true, true) => from_bits <= to_bits,
                            (false, true) => from_bits < to_bits, // one bit reserved for the sign
                            (true, false) => false,               // a negative source never fits
                        };
                        if lossless {
                            arg_prim
                        } else {
                            // Truncate to the target width and reinterpret with its
                            // signedness (two's complement); the shared helper wraps
                            // `((x [+ 2^(N-1)]) mod 2^N) [- 2^(N-1)]`.
                            vcx.get_wrapped_val(arg_prim.downcast_ty(), result_kind)
                                .upcast_ty()
                        }
                    };
                    let expr = e_res_ty.prim_to_snap(wrapped);

                    let fn_idn = FunctionIdn::new(name, op_ty_snap, res_ty_snap);
                    let function = vcx.mk_function(fn_idn, (arg_decl,), &[], &[], None, Some(expr));
                    (
                        MirBuiltinCastLocal {
                            cast: function,
                            unsize: None,
                            undo: None,
                        },
                        MirBuiltinCastOutput::Simple(fn_idn),
                    )
                }
                mir::CastKind::PtrToPtr => {
                    let e_op_ty = op_ty.expect_raw();
                    let e_res_ty = res_ty.expect_raw();
                    let expr = e_res_ty.prim_to_snap(
                        e_op_ty.address_access(arg_ex),
                        e_op_ty.metadata_access(arg_ex),
                    );

                    let fn_idn = FunctionIdn::new(name, op_ty_snap, res_ty_snap);
                    let function = vcx.mk_function(fn_idn, (arg_decl,), &[], &[], None, Some(expr));
                    (
                        MirBuiltinCastLocal {
                            cast: function,
                            unsize: None,
                            undo: None,
                        },
                        MirBuiltinCastOutput::Simple(fn_idn),
                    )
                }
                mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _) => {
                    // Unsizing preserves the (wide) reference snapshot type and only
                    // rewrites the pointer metadata for the new referent. The cast
                    // (like the methods below) is parameterized by the operand and
                    // result referent types `U`, `V`, which `MirBuiltinUseCastEnc`
                    // supplies from each reference's referent arg. The metadata type
                    // is now *derived* from the referent (not a separate reference
                    // type param), so we declare these two type params explicitly
                    // here as a fresh `[U, V]` context (`unsize_params`) rather than
                    // piggybacking on the reference's own generics.
                    assert_eq!(op_ty_snap, res_ty_snap);
                    let unsize_gparams = {
                        let u = ty::Ty::new_param(vcx.tcx(), 0, symbol::Symbol::intern("U"));
                        let v = ty::Ty::new_param(vcx.tcx(), 1, symbol::Symbol::intern("V"));
                        GParams::empty_env(vcx.tcx().mk_args(&[u.into(), v.into()]))
                    };
                    let unsize_params = deps.require_dep::<GenericParamsEnc>(unsize_gparams)?;
                    let u = unsize_params.ty_exprs()[0];
                    let v = unsize_params.ty_exprs()[1];
                    let value_cast = deps.require_dep::<ValueCastEnc>(())?;
                    let (is_mut, metadata, res_cons) = match &op_ty.specifics {
                        TySpecifics::ImmRef(data) => {
                            let res_data = res_ty.expect_immref();
                            let value = value_cast(data.value_access(arg_ex).downcast_ty(), u, v)
                                .upcast_ty();
                            let res_cons = |metadata| {
                                res_data.prim_to_snap(data.deref_access(arg_ex), metadata, value)
                            };
                            (
                                false,
                                data.metadata_access(arg_ex).downcast_ty(),
                                Ok(res_cons),
                            )
                        }
                        TySpecifics::MutRef(data) => {
                            let res_data = res_ty.expect_mutref();
                            let res_cons = |metadata| {
                                res_data.prim_to_snap(
                                    data.deref_access(arg_ex),
                                    metadata,
                                    data.value_access(arg_ex),
                                )
                            };
                            (
                                true,
                                data.metadata_access(arg_ex).downcast_ty(),
                                Err(res_cons),
                            )
                        }
                        _ => unreachable!(),
                    };
                    // `metadata_cast(old_metadata, U, V)` rewrites the (operand)
                    // metadata for the result referent type `V` (e.g. a thin unit
                    // metadata becomes a slice length, or a `dyn` vtable).
                    let metadata_cast = deps.require_dep::<MetadataCastEnc>(())?;
                    let metadata = metadata_cast(
                        metadata,
                        unsize_params.ty_exprs()[0],
                        unsize_params.ty_exprs()[1],
                    );
                    let expr = match res_cons {
                        Ok(res_cons) => res_cons(metadata.upcast_ty()),
                        Err(res_cons) => res_cons(metadata.upcast_ty()),
                    };
                    let fn_idn = FunctionIdn::new(
                        name,
                        (
                            op_ty_snap,
                            unsize_params.ty_args(),
                            unsize_params.const_args(),
                        ),
                        res_ty_snap,
                    );
                    let function = vcx.mk_function(
                        fn_idn,
                        (
                            arg_decl,
                            unsize_params.ty_decls(),
                            unsize_params.const_decls(),
                        ),
                        &[],
                        &[],
                        None,
                        Some(expr),
                    );
                    // For `&mut` coercions, generate the side-effecting
                    // `unsize`/`undo` methods that move the (generic) `p_Param`
                    // predicate of the referent between the operand and result type
                    // at the same address (the coercion preserves it). The methods
                    // are declared over the fresh `[U, V]` type params
                    // (`unsize_params`), which `MirBuiltinUseCastEnc` instantiates
                    // with the operand referent `U` and result referent `V`.
                    // `new_param_ty(i).decompose(unsize_gparams)` builds a `Param`
                    // decomposition whose arg is `unsize_gparams`' `i`th type
                    // variable, so `ref_to_pred`/`ref_to_snap` yield
                    // `p_Param(addr, U)` / `p_Param(addr, V)` directly; the referent
                    // snapshot is transferred via `value_cast` (whose concrete-type
                    // axioms are added in `MirBuiltinUseCastEnc`).
                    let (unsize_method, undo_method, unsize_idn, undo_idn) = if is_mut {
                        let u_impure = deps.require_dep::<TyUseImpureEnc>(
                            LazyRustTy::new_param_ty(0).decompose(unsize_gparams),
                        )?;
                        let v_impure = deps.require_dep::<TyUseImpureEnc>(
                            LazyRustTy::new_param_ty(1).decompose(unsize_gparams),
                        )?;

                        let src_mutref = op_ty.expect_mutref();
                        let src_decl = vcx.mk_local_decl("src", op_ty_snap);
                        let src_ex = vcx.mk_local_ex(src_decl);
                        let addr = src_mutref.deref_access(src_ex);

                        let u_pred = u_impure.ref_to_pred(vcx, addr, None);
                        let v_pred = v_impure.ref_to_pred(vcx, addr, None);
                        let u_snap = u_impure.ref_to_snap(addr).downcast_ty::<vir::PSnap>();
                        let v_snap = v_impure.ref_to_snap(addr).downcast_ty::<vir::PSnap>();

                        // `unsize`: operand referent `U` -> result referent `V`; the
                        // new `V` value is `value_cast(old(U), U, V)`. `undo` is the
                        // *reverse* equation: the old `V` value is `value_cast` of the
                        // recovered `U` value, `old(V) == value_cast(U, U, V)`. Both
                        // use the same `value_cast` direction (`U, V`), so a single
                        // axiom per coercion (added in `MirBuiltinUseCastEnc`) suffices.
                        let unsize_value =
                            vcx.mk_eq_expr(v_snap, value_cast(vcx.mk_old_expr(u_snap), u, v));
                        let undo_value =
                            vcx.mk_eq_expr(vcx.mk_old_expr(v_snap), value_cast(u_snap, u, v));

                        let unsize_idn = MethodIdn::new(
                            vir::vir_format_identifier!(
                                vcx,
                                "mir_unsize_{}_to_{}",
                                operand_ty.name(),
                                result_ty.name()
                            ),
                            (
                                op_ty_snap,
                                unsize_params.ty_args(),
                                unsize_params.const_args(),
                            ),
                        );
                        let undo_idn = MethodIdn::new(
                            vir::vir_format_identifier!(
                                vcx,
                                "mir_undo_unsize_{}_to_{}",
                                operand_ty.name(),
                                result_ty.name()
                            ),
                            (
                                op_ty_snap,
                                unsize_params.ty_args(),
                                unsize_params.const_args(),
                            ),
                        );
                        let unsize_method = vcx.mk_method(
                            unsize_idn,
                            (
                                src_decl,
                                unsize_params.ty_decls(),
                                unsize_params.const_decls(),
                            ),
                            &[],
                            vcx.alloc_slice(&[u_pred]),
                            vcx.alloc_slice(&[v_pred, unsize_value]),
                            None,
                        );
                        let undo_method = vcx.mk_method(
                            undo_idn,
                            (
                                src_decl,
                                unsize_params.ty_decls(),
                                unsize_params.const_decls(),
                            ),
                            &[],
                            vcx.alloc_slice(&[v_pred]),
                            vcx.alloc_slice(&[u_pred, undo_value]),
                            None,
                        );
                        (
                            Some(unsize_method),
                            Some(undo_method),
                            Some(unsize_idn),
                            Some(undo_idn),
                        )
                    } else {
                        (None, None, None, None)
                    };
                    (
                        MirBuiltinCastLocal {
                            cast: function,
                            unsize: unsize_method,
                            undo: undo_method,
                        },
                        MirBuiltinCastOutput::Unsize {
                            cast: fn_idn,
                            unsize: unsize_idn,
                            undo: undo_idn,
                        },
                    )
                }
                _ => todo!("cast kind {kind:?}"),
            };
            Ok(output)
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for local in Self::all_outputs_local_no_errors(program) {
            program.add_function(local.cast);
            if let Some(unsize) = local.unsize {
                program.add_method(unsize);
            }
            if let Some(undo) = local.undo {
                program.add_method(undo);
            }
        }
    }
}
