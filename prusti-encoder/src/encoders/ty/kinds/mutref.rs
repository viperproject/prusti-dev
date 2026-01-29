use crate::encoders::ty::{
    RustMutRef,
    impure::{PredicateBuilder, TyImpureEnc, TyImpureMutRef, TyImpureMutRefData},
    pure::{AdtBuilder, TyPureEnc, TyPureMutRef, TyPureMutRefData},
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::CastType;

pub(crate) fn ty_pure<'vir>(
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureMutRef<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let (field_snaps_to_snap, field_access) =
        builder.constructor("", (vir::TYPE_REF, vir::TYPE_PSNAP), None);

    Ok(TyPureMutRefData {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
        value_access: field_access[1].downcast_ty(),
    })
}

pub(crate) fn ty_impure<'vir>(
    data: &(&RustMutRef<'vir>, &TyPureMutRef<'vir>),
    _deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureMutRef<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.csnap_type();
    let ref_param = builder.vcx.mk_local_decl("r", vir::TYPE_REF);
    let ref_param_ex = builder.vcx.mk_local_ex(ref_param);
    let arbitrary_value = builder.inner.function(
        "arbitrary_value",
        vir::TYPE_REF,
        snap_type,
        (ref_param,),
        &[],
        &[vir::expr! {
            ([data.1.deref_access](result: [snap_type])) == ([ref_param_ex])
        }],
        None,
    );

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // fields
    let ref_field = builder.field("val", snap_type);

    // main predicate
    builder.mk_predicate("", Some(vir::expr! { acc((ref_self).[ref_field]) }));

    // Ref-to-snap
    builder.mk_snap_function(Some(vir::expr! { [ref_field](ref_self) }));

    Ok(TyImpureMutRefData {
        pure: *data.1,
        arbitrary_value,
    })
}
