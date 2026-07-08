use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{
    Pure,
    builtin::{MetadataCastEnc, ValueCastEnc},
    ty::{
        RustTy, RustTyDecomposition, RustTyNormalized, TySpecifics,
        generics::{GArgs, GArgsCastEnc, GenericParamsEnc},
        lifted::TyConstructorEnc,
        use_pure::TyUsePureEnc,
    },
};

/// Emits the metadata rewrite for a concrete `[T; N] -> [T]` (array-to-slice)
/// coercion: an axiom defining `metadata_cast(_, [T; N], [T])` as the array's
/// static length `N` - the fat-pointer metadata of the resulting slice. Like
/// `ValueCastAxiomEnc`, it is keyed on the *generic* array/slice shapes (the
/// `RustTy`, shared by every `[T; N]`), so it is encoded once and is itself
/// generic over the element type and length. The abstract `metadata_cast`
/// function and its identity axiom live in `MetadataCastEnc`; this encoder
/// attaches only the array->slice specialization (so `MetadataCastEnc` no longer
/// has to assume that array/slice types exist in the program).
pub struct MetadataCastAxiomEnc;

impl TaskEncoder for MetadataCastAxiomEnc {
    task_encoder::encoder_cache!(MetadataCastAxiomEnc);
    const ENCODER_NAME: &'static str = "metadata cast axiom encoder";

    type TaskDescription<'vir> = (RustTy<'vir>, RustTy<'vir>);
    type OutputFullLocal<'vir> = Option<vir::Domain<'vir>>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (array_ty, slice_ty) = *task_key;
        match (&array_ty.specifics, &slice_ty.specifics) {
            (TySpecifics::ArrayLike(ad), TySpecifics::ArrayLike(sd)) if !ad.slice && sd.slice => {}
            _ => return Ok((None, ())),
        }

        let metadata_cast = deps.require_dep::<MetadataCastEnc>(())?;
        let array_ctor = deps.require_ref::<TyConstructorEnc>(array_ty)?;
        let slice_ctor = deps.require_ref::<TyConstructorEnc>(slice_ty)?;
        // Quantify over the array's own params (`T`, `N`), so the axiom is generic
        // over every `[T; N]` rather than baking in a concrete element/length.
        let array_gen = deps.require_dep::<GenericParamsEnc>(array_ty.params)?;
        // The slice metadata is the array's length `N`, held generically (as a
        // `p_Param` snapshot); cast the concrete `usize` length into the generic
        // context via `usize`'s pure caster.
        let usize = RustTyDecomposition::from_prim_ty(vir::with_vcx(|vcx| vcx.tcx().types.usize));
        let len_caster = deps.require_dep::<GArgsCastEnc<Pure>>(Some(RustTyNormalized {
            param: RustTyDecomposition::param(),
            concrete: usize,
        }))?;

        vir::with_vcx(|vcx| {
            // The (generic) array/slice referent type values `[T; N]` / `[T]`, in the
            // same form the `cast` fn passes as `metadata_cast`'s `[U, V]`.
            let u_ty = (array_ctor.ty_constructor)(array_gen.ty_exprs(), array_gen.const_exprs());
            let v_ty = (slice_ctor.ty_constructor)(array_gen.ty_exprs(), &[]);
            // The array's single const param `N`, made generic.
            let len = array_gen.const_exprs()[0];
            let len_generic = len_caster
                .cast_to_callee_ctx(len.upcast_ty())
                .downcast_ty::<vir::PSnap>();

            let input_decl = vcx.mk_local_decl("input", vir::TYPE_PSNAP);
            let input = vcx.mk_local_ex(input_decl);
            let call = metadata_cast(input, u_ty, v_ty);
            let body = vcx.mk_eq_expr(call, len_generic);
            // forall input, T, N :: { metadata_cast(input, [T; N], [T]) }
            //     metadata_cast(input, [T; N], [T]) == make_generic_usize(N)
            let axiom_expr = vir::expr! {
                forall [input_decl], ..[array_gen.ty_decls()], ..[array_gen.const_decls()]
                    :: { [call] }
                    [body]
            };
            let axiom = vcx.mk_domain_axiom(
                vir::ViperIdent::new("metadata_cast_array_slice"),
                axiom_expr,
            );
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("MetadataCastArraySlice"),
                &[],
                vcx.alloc_slice(&[axiom]),
                &[],
                None,
            );
            Ok((Some(domain), ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            let Some(domain) = domain else {
                continue;
            };
            program.add_domain(domain);
        }
    }
}

/// Emits the functional specification of `unsize_value_cast` for a concrete
/// `[T; N] -> [T]` (array-to-slice) coercion: an axiom stating that the coerced
/// slice has the same elements as the original array (the length is carried by
/// the fat-pointer metadata, set by `metadata_cast`). The coercion's referent
/// value is held as a generic `p_Param`, so the relation is expressed by
/// `make_concrete`-ing both sides to their `[T; N]`/`[T]` snapshots and comparing
/// elements. Keyed on the *generic* array/slice shapes (the `RustTy`, shared by
/// every `[T; N]`), so it is encoded once and is itself generic over the element
/// type `T` and length `N`. The abstract `unsize_value_cast` function and its
/// identity axiom live in `ValueCastEnc`; this encoder attaches only the
/// array->slice specialization.
pub struct ValueCastAxiomEnc;

impl TaskEncoder for ValueCastAxiomEnc {
    task_encoder::encoder_cache!(ValueCastAxiomEnc);
    const ENCODER_NAME: &'static str = "value cast axiom encoder";

    type TaskDescription<'vir> = (RustTy<'vir>, RustTy<'vir>);
    type OutputFullLocal<'vir> = Option<vir::Domain<'vir>>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (array_ty, slice_ty) = *task_key;
        match (&array_ty.specifics, &slice_ty.specifics) {
            (TySpecifics::ArrayLike(ad), TySpecifics::ArrayLike(sd)) if !ad.slice && sd.slice => {}
            _ => return Ok((None, ())),
        }

        // The most-generic array/slice (identity args), so the axiom quantifies
        // over the element/length params rather than baking in a concrete `[T; N]`.
        let array_inner = RustTyDecomposition::identity(array_ty);
        let mut slice_inner = RustTyDecomposition::identity(slice_ty);

        // Re-base the slice's element onto the array's element type parameter: a
        // valid `[T; N] -> [T]` coercion always has matching element types, so
        // the axiom quantifies over the array's params only (`U`, `M`) and the
        // slice reuses the array's element `U`. This is also what lets the
        // concrete-keyed axiom below trigger without a free slice-element var.
        slice_inner.args = GArgs::new(
            array_ty.params,
            vir::with_vcx(|vcx| vcx.tcx().mk_args(&[array_ty.params.rust_params()[1]])),
        );

        let value_cast = deps.require_dep::<ValueCastEnc>(())?;
        let array_use = deps.require_dep::<TyUsePureEnc>(array_inner)?;
        let slice_use = deps.require_dep::<TyUsePureEnc>(slice_inner)?;
        let array_ctor = deps.require_ref::<TyConstructorEnc>(array_ty)?;
        let slice_ctor = deps.require_ref::<TyConstructorEnc>(slice_ty)?;
        let array_gen = deps.require_dep::<GenericParamsEnc>(array_ty.params)?;
        let param = RustTyDecomposition::param();
        let array_caster = deps.require_dep::<GArgsCastEnc<Pure>>(Some(RustTyNormalized {
            param,
            concrete: array_inner,
        }))?;
        let slice_caster = deps.require_dep::<GArgsCastEnc<Pure>>(Some(RustTyNormalized {
            param,
            concrete: slice_inner,
        }))?;

        vir::with_vcx(|vcx| {
            let array_pure = array_use.expect_array();
            let slice_pure = slice_use.expect_array();
            // The (generic) referent type values `[T; N]` and `[T]`, in the same
            // form `MirBuiltinUseCastEnc` passes as the `unsize`/`undo` method's
            // `U`/`V` type arguments. The slice element is the array's element `U`
            // (see `slice_args`).
            let u_ty = (array_ctor.ty_constructor)(array_gen.ty_exprs(), array_gen.const_exprs());
            let v_ty = (slice_ctor.ty_constructor)(array_gen.ty_exprs(), &[]);

            let arr_decl = vcx.mk_local_decl("arr", array_use.snapshot.downcast_ty());
            let arr = vcx.mk_local_ex(arr_decl);
            let arr_generic = array_caster
                .cast_to_callee_ctx(arr.upcast_ty())
                .downcast_ty::<vir::PSnap>();
            let arr_vc = value_cast(arr_generic, u_ty, v_ty);
            let sli = slice_caster
                .cast_to_caller_ctx(arr_vc.upcast_ty())
                .downcast_ty::<vir::CSnap>();

            let idx_decl = vcx.mk_local_decl("idx", vir::TYPE_INT);
            let idx = vcx.mk_local_ex(idx_decl);
            // Compare the elements in their generic (`p_Param`) form: the array and
            // slice share the same element type, so the concrete element conversion
            // would be redundant.
            let idx_body = vcx.mk_eq_expr(
                array_pure.index_generic(arr, idx),
                slice_pure.index_generic(sli, idx),
            );
            let idx_forall = vcx.mk_forall_expr(
                vcx.alloc_slice(&[idx_decl]),
                vcx.alloc_slice(&[vcx.mk_trigger(&[array_pure.index_generic(arr, idx)])]),
                idx_body,
            );
            let axiom_expr = vir::expr! {
                forall [arr_decl], ..[array_gen.ty_decls()], ..[array_gen.const_decls()]
                    :: { [arr_vc] }
                    [idx_forall]
            };
            let axiom = vcx.mk_domain_axiom(
                vir::ViperIdent::new("unsize_value_cast_array_slice"),
                axiom_expr,
            );

            let domain = vcx.mk_domain(
                vir::ViperIdent::new("UnsizeValueCastArraySlice"),
                &[],
                vcx.alloc_slice(&[axiom]),
                &[],
                None,
            );
            Ok((Some(domain), ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            let Some(domain) = domain else {
                continue;
            };
            program.add_domain(domain);
        }
    }
}
