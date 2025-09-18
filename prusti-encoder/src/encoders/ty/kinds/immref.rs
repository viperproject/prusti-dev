use crate::encoders::ty::{
    impure::{ImpureTyDatas, PredicateBuilder, TyImpureEnc, TyImpureImmRef, TyImpureImmRefData}, lifted::TypeOfEnc, pure::{AdtBuilder, PureTyDatas, TyPureEnc, TyPureImmRef, TyPureImmRefData}, RustTyDatas, RustImmRef
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

pub(crate) fn ty_pure<'vir>(
    _data: &RustImmRef<'vir>,
    _deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureImmRef<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let (field_snaps_to_snap, field_access) = builder.constructor("", (vir::TYPE_REF, vir::TYPE_PSNAP), None);

    Ok(TyPureImmRefData {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
        value_access: field_access[1].downcast_ty(),
    })
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustImmRef<'vir>, &TyPureImmRef<'vir>),
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    TyImpureImmRef<'vir>,
    EncodeFullError<'vir, TyImpureEnc>,
> {
    let snap_type = builder.csnap_type();

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // let generic_typeof = TypeOfEnc::generic_typeof(deps);

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    let self_pred = builder.inner.predicate::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>(
        "",
        (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args()),
    (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
        Some(vir::expr! {
            acc((ref_self).[ref_field])
            // TODO: pure typeof assertions do not currently work
            // && (([generic_typeof]([data.1.value_access]([ref_field](ref_self)))) == ([builder.params.ty_exprs()[0]]))
        }), // TODO: use generic args?
    );

    // Ref-to-snap
    builder.function_snap = Some(builder.mk_function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), _>(
        "snap",
        (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args()),
        snap_type,
        (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
        &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
        &[], // vir::expr! { ([generic_typeof]([data.1.value_access](result: [snap_type]))) == ([builder.params.ty_exprs()[0]]) }],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([ref_field](ref_self))
        }),
    ).1);

    // Ref-to-Ref
    let deref_func = builder.inner.function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), _>(
        "deref",
        (ref_self_decl.ty(), builder.params.ty_args(), builder.params.const_args()),
        vir::TYPE_REF,
        (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
        &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
        &[],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([data.1.deref_access]([ref_field](ref_self)))
        }),
    );

    Ok(TyImpureImmRefData {
        deref_func,
    })
}
