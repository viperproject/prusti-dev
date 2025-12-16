use crate::encoders::ty::{
    RustRawPtr,
    impure::{PredicateBuilder, TyImpureEnc, TyImpureRawPtr, TyImpureRawPtrData},
    pure::{AdtBuilder, TyPureEnc, TyPureRawPtr, TyPureRawPtrData},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, HasType};

pub(crate) fn ty_pure<'vir>(
    _data: &RustRawPtr<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureRawPtr<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let (field_snaps_to_snap, field_access) =
        builder.constructor("", vir::TYPE_REF, None);

    Ok(TyPureRawPtrData {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
    })
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustRawPtr<'vir>, &TyPureRawPtr<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureRawPtr<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.snap_type();

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder
        .inner
        .predicate::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>(
            "",
            (
                ref_self_decl.ty(),
                builder.params.ty_args(),
                builder.params.const_args(),
            ),
            (
                ref_self_decl,
                builder.params.ty_decls(),
                builder.params.const_decls(),
            ),
            Some(vir::expr! { acc((ref_self).[ref_field]) }),
        );

    // Ref-to-snap
    builder.function_snap = Some(
        builder
            .mk_function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), _>(
                "snap",
                (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args()),
                snap_type,
                (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
                &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
                &[],
                Some(vir::expr! {
                    unfolding ([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([ref_field](ref_self))
                }),
            )
            .1,
    );

    // Ref-to-Ref
    let deref_func = builder.inner.function(
        "deref",
        (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args()),
        vir::TYPE_REF,
        (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
        &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
        &[],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([data.1.deref_access](([ref_field](ref_self)) as CSnap))
        }),
    );

    Ok(TyImpureRawPtrData { deref_func })
}