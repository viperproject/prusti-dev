use crate::encoders::{
    TyUseImpureEnc, TyUsePureEnc,
    ty::{
        RustMutRef, RustTyDatas,
        data::TyData,
        impure::{PredicateBuilder, TyImpureEnc, TyImpureMutRef, TyImpureMutRefData},
        pure::{AdtBuilder, PureTyDatas, TyPureEnc, TyPureMutRef, TyPureMutRefData},
    },
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::CastType;

pub(crate) fn ty_pure<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &RustMutRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureMutRef<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let ty = data.metadata.decompose(task_key.params);
    let metadata = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot.downcast_ty();

    let ty = data.referent.decompose(task_key.params);
    let referent = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot.downcast_ty();

    let (field_snaps_to_snap, field_access) =
        builder.constructor("", (vir::TYPE_REF, metadata, referent), None);

    Ok(TyPureMutRefData {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
        metadata_access: field_access[1].downcast_ty(),
        value_access: field_access[2].downcast_ty(),
    })
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &(&RustMutRef<'vir>, &TyPureMutRef<'vir>),
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureMutRef<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let snap_type = builder.csnap_type();
    let ref_param = builder.vcx.mk_local_decl("r", vir::TYPE_REF);
    let ref_ex = builder.vcx.mk_local_ex(ref_param);

    let metadata_type = data.0.metadata.decompose(task_key.0.params);
    deps.require_dep::<TyUseImpureEnc>(metadata_type)?;
    let inner_type = data.0.referent.decompose(task_key.0.params);
    deps.require_dep::<TyUseImpureEnc>(inner_type)?;

    let metadata_type = deps
        .require_ref::<TyUsePureEnc>(metadata_type)?
        .snapshot
        .downcast_ty();
    let metadata_param = builder.vcx.mk_local_decl("metadata", metadata_type);
    let metadata_ex = builder.vcx.mk_local_ex(metadata_param);
    let arbitrary_value = builder.inner.function(
        "arbitrary_value",
        (vir::TYPE_REF, metadata_type),
        snap_type,
        (ref_param, metadata_param),
        &[],
        &[
            vir::expr! {
                ([data.1.deref_access](result: [snap_type])) == ([ref_ex])
            },
            vir::expr! {
                ([data.1.metadata_access](result: [snap_type])) == ([metadata_ex])
            },
        ],
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
