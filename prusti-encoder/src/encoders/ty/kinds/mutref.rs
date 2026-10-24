use crate::encoders::{
    TyUseImpureEnc, TyUsePureEnc,
    ty::{
        RustMutRef, RustTyDatas,
        data::TyData,
        generics::{ParamTypEnc, TyExprEnc},
        impure::{PredicateBuilder, TyImpureEnc, TyImpureMutRef, TyImpureMutRefData},
        pure::{AdtBuilder, PureTyDatas, TyPureEnc, TyPureMutRef, TyPureMutRefData},
    },
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CallableIdn, CastType};

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

    let (field_snaps_to_snap_shallow, field_access_shallow) =
        builder.constructor("shallow", (vir::TYPE_REF, metadata), None);

    let deep_snap_fields: (
        vir::AdtDestructor<'vir, vir::CSnap, vir::Ref>,
        vir::AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
        vir::AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
    ) = (
        field_access[0].downcast_ty(),
        field_access[1].downcast_ty(),
        field_access[2].downcast_ty(),
    );
    let shallow_snap_fields: (
        vir::AdtDestructor<'vir, vir::CSnap, vir::Ref>,
        vir::AdtDestructor<'vir, vir::CSnap, vir::PSnap>,
    ) = (
        field_access_shallow[0].downcast_ty(),
        field_access_shallow[1].downcast_ty(),
    );

    // The address and metadata of a snapshot, whether it was built with the
    // deep or the shallow constructor.
    let vcx = builder.vcx;
    let snap_decl = vcx.mk_local_decl("snap", builder.self_type());
    let snap = vcx.mk_local_ex(snap_decl);
    let is_shallow =
        vcx.mk_adt_discriminator_expr(snap, field_snaps_to_snap_shallow.name().to_str());
    let addr = builder.function(
        "addr",
        builder.self_type(),
        vir::TYPE_REF,
        (snap_decl,),
        &[],
        &[],
        Some(vcx.mk_ternary_expr(
            is_shallow,
            shallow_snap_fields.0.call()(snap),
            deep_snap_fields.0.call()(snap),
        )),
    );
    let metadata_fn = builder.function(
        "metadata",
        builder.self_type(),
        metadata,
        (snap_decl,),
        &[],
        &[],
        Some(vcx.mk_ternary_expr(
            is_shallow,
            shallow_snap_fields.1.call()(snap),
            deep_snap_fields.1.call()(snap),
        )),
    );

    Ok(TyPureMutRefData {
        prim_to_deep_snap: field_snaps_to_snap,
        prim_to_shallow_snap: field_snaps_to_snap_shallow,
        deep_snap_fields,
        shallow_snap_fields,
        addr,
        metadata: metadata_fn,
    })
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &(&RustMutRef<'vir>, &TyPureMutRef<'vir>),
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureMutRef<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let metadata_decomp = data.0.metadata.decompose(task_key.0.params);
    deps.require_dep::<TyUseImpureEnc>(metadata_decomp)?;
    let inner_type = data.0.referent.decompose(task_key.0.params);
    let inner_type_impure = deps.require_dep::<TyUseImpureEnc>(inner_type)?;

    let snap_type = builder.csnap_type_shallow();
    let metadata_type = deps
        .require_ref::<TyUsePureEnc>(metadata_decomp)?
        .snapshot
        .downcast_ty();

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);
    let vcx = builder.vcx;

    let addr_field = builder.field("addr", vir::TYPE_REF);
    let metadata_field = builder.field("metadata", metadata_type);

    let metadata_ty = deps.require_dep::<TyExprEnc>(metadata_decomp)?;
    let typ = deps.require_dep::<ParamTypEnc>(())?.typ;
    let metadata_typ = |metadata| vcx.mk_eq_expr(typ(metadata), metadata_ty);

    let referent_ty = deps.require_dep::<TyExprEnc>(inner_type)?;

    // main predicate
    builder.mk_predicate(
        "",
        Some(vcx.mk_conj(&[
            vir::expr! { acc((ref_self).[addr_field]) },
            vir::expr! { acc((ref_self).[metadata_field]) },
            metadata_typ(vir::expr! { [metadata_field](ref_self) }),
        ])),
    );

    let addr = vir::expr! { [addr_field](ref_self) };
    let metadata = vir::expr! { [metadata_field](ref_self) };

    // Ref-to-snap
    builder.mk_shallow_snap_function(
        Some(data.1.prim_to_shallow_snap.call()(addr, metadata)),
        &[metadata_typ(data.1.shallow_snap_fields.1.call()(
            vcx.mk_result(snap_type),
        ))],
    );
    let shallow_addr = data.1.shallow_snap_fields.0.call()(
        builder.ref_to_shallow_snap.call()(
            ref_self,
            builder.params.ty_exprs(),
            builder.params.const_exprs(),
        )
        .downcast_ty(),
    );
    builder.mk_deep_snap_function(
        Some(data.1.prim_to_deep_snap.call()(
            addr,
            metadata,
            inner_type_impure.ref_to_deep_snap(addr).downcast_ty(),
        )),
        &[inner_type_impure.ref_to_pred(vcx, shallow_addr, None)],
        &[
            metadata_typ(data.1.deep_snap_fields.1.call()(
                vcx.mk_result(builder.csnap_type_deep()),
            )),
            vcx.mk_eq_expr(
                typ(data.1.deep_snap_fields.2.call()(
                    vcx.mk_result(builder.csnap_type_deep()),
                )),
                referent_ty,
            ),
        ],
    );

    Ok(TyImpureMutRefData { pure: *data.1 })
}
