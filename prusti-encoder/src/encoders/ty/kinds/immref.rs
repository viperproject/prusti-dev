use crate::encoders::{
    TyUseImpureEnc, TyUsePureEnc,
    custom::ReadPermEnc,
    ty::{
        RustImmRef, RustTyDatas, RustTyDecomposition,
        data::TyData,
        generics::{ParamTypEnc, TyExprEnc},
        impure::{PredicateBuilder, TyImpureEnc, TyImpureImmRef, TyImpureImmRefData},
        pure::{AdtBuilder, PureTyDatas, TyPureEnc, TyPureImmRef, TyPureImmRefData},
    },
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::CastType;

pub(crate) fn ty_pure<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &RustImmRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<TyPureImmRef<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let ty = data.metadata.decompose(task_key.params);
    let metadata = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot.downcast_ty();

    let ty = data.referent.decompose(task_key.params);
    let referent = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot.downcast_ty();

    let (field_snaps_to_snap, field_access) =
        builder.constructor("", (vir::TYPE_REF, metadata, referent), None);

    Ok(TyPureImmRefData {
        prim_to_snap: field_snaps_to_snap,
        deref_access: field_access[0].downcast_ty(),
        metadata_access: field_access[1].downcast_ty(),
        value_access: field_access[2].downcast_ty(),
    })
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &(&RustImmRef<'vir>, &TyPureImmRef<'vir>),
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<TyImpureImmRef<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let metadata_type = data.0.metadata.decompose(task_key.0.params);
    deps.require_dep::<TyUseImpureEnc>(metadata_type)?;
    let inner_type = data.0.referent.decompose(task_key.0.params);
    deps.require_dep::<TyUseImpureEnc>(inner_type)?;

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    let metadata_snap = deps
        .require_ref::<TyUsePureEnc>(metadata_type)?
        .snapshot
        .downcast_ty();

    // fields: the referent's address and the pointer metadata. The referent's
    // value is not stored; it is read out of the `p_Param` held below, which
    // is what ties it to the type this predicate is instantiated at.
    let addr_field = builder.field("addr", vir::TYPE_REF);
    let metadata_field = builder.field("metadata", metadata_snap);

    let vcx = builder.vcx;
    let read = deps.require_dep::<ReadPermEnc>(())?.read;
    let param_ty = deps.require_ref::<TyImpureEnc>(RustTyDecomposition::param())?;
    let referent_ty = deps.require_dep::<TyExprEnc>(inner_type)?;
    let metadata_ty = deps.require_dep::<TyExprEnc>(metadata_type)?;
    let addr = vir::expr! { [addr_field](ref_self) };
    let referent_pred = vcx.mk_predicate_app_expr((param_ty.ref_to_pred)(
        addr,
        vcx.alloc_slice(&[referent_ty]),
        &[],
    )(Some(read())));
    // Unlike the referent, the metadata is stored rather than held as a
    // `p_Param`, so its type has to be stated for the variant bridge.
    let typ = deps.require_dep::<ParamTypEnc>(())?.typ;
    let metadata_typ = |metadata| vcx.mk_eq_expr(typ(metadata), metadata_ty);

    // main predicate
    builder.mk_predicate(
        "",
        Some(vcx.mk_conj(&[
            vir::expr! { acc((ref_self).[addr_field]) },
            vir::expr! { acc((ref_self).[metadata_field]) },
            metadata_typ(vir::expr! { [metadata_field](ref_self) }),
            referent_pred,
        ])),
    );

    // Ref-to-snap: the referent's value comes from the `p_Param` above, whose
    // snapshot carries its type, so the type is known by construction.
    builder.mk_snap_function(
        Some(data.1.prim_to_snap.call()(
            addr,
            vir::expr! { [metadata_field](ref_self) },
            (param_ty.ref_to_snap)(addr, vcx.alloc_slice(&[referent_ty]), &[]).downcast_ty(),
        )),
        &[
            metadata_typ(data.1.metadata_access.call()(
                vcx.mk_result(builder.csnap_type()),
            )),
            vcx.mk_eq_expr(
                typ(data.1.value_access.call()(
                    vcx.mk_result(builder.csnap_type()),
                )),
                referent_ty,
            ),
        ],
    );

    Ok(TyImpureImmRefData {})
}
