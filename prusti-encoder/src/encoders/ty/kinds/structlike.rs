use crate::encoders::{
    TyUseImpureEnc,
    ty::{
        RustTyDatas,
        data::{StructData, TyData},
        impure::{
            ImpureTyDatas, PredicateBuilder, TyImpureEnc, TyImpureFieldData, TyImpureStructData,
        },
        pure::{
            AdtBuilder, PureTyDatas, TyPureEnc, TyPureFieldData, TyPureFieldRef, TyPureStructData,
        },
        rust_ty::{RustFieldAddress, RustTySpecial},
        use_pure::TyUsePureEnc,
    },
};
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{CastType, HasType, PredicateIdn};

pub(crate) fn ty_pure<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &StructData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<StructData<'vir, PureTyDatas>, EncodeFullError<'vir, TyPureEnc>> {
    ty_pure_variant("", None, task_key, data, deps, builder)
}

pub(super) fn ty_pure_variant<'vir>(
    prefix: &str,
    discr: Option<vir::ExprCSnap<'vir>>,
    task_key: &TyData<'vir, RustTyDatas>,
    data: &StructData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<StructData<'vir, PureTyDatas>, EncodeFullError<'vir, TyPureEnc>> {
    let field_tys = data
        .fields
        .iter()
        .map(|f| {
            let ty = f.decompose(task_key.params);
            Ok(deps.require_ref::<TyUsePureEnc>(ty)?.snapshot)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let field_tys = builder.vcx.alloc_slice(&field_tys);
    let (field_snaps_to_snap, des) = builder.constructor(prefix, field_tys, discr);

    // For a `Box`, its extras and the address of its (dynamic) value field.
    let box_data = if let RustTySpecial::Box = task_key.special {
        Some(super::r#box::mk_pure_box_data(
            task_key, data, deps, builder,
        )?)
    } else {
        None
    };

    let ref_self_decl = builder.vcx.mk_local_decl("self", vir::TYPE_REF);
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);
    let params = builder.params.clone();

    assert_eq!(des.len(), data.fields.len());
    let des = des
        .iter()
        .zip(&data.fields)
        .enumerate()
        .map(|(idx, (read, field))| {
            let ref_to_field_ref = match field.address {
                RustFieldAddress::Constant => {
                    let args = (ref_self_decl.ty(), params.ty_args(), params.const_args());
                    let params = (ref_self_decl, params.ty_decls(), params.const_decls());
                    TyPureFieldRef::Constant(builder.function(
                        &format!("{prefix}field_{idx}"),
                        args,
                        vir::TYPE_REF,
                        params,
                        &[],
                        &[vir::expr! { ((ref_self) == (null)) == ((result: Ref) == (null)) }],
                        None,
                    ))
                }
                RustFieldAddress::Dynamic => TyPureFieldRef::Dynamic(box_data.unwrap().1),
            };
            TyPureFieldData {
                read: read.downcast_ty(),
                ref_to_field_ref,
            }
        })
        .collect::<Vec<_>>();
    Ok(StructData::new(
        TyPureStructData {
            field_snaps_to_snap,
            box_data: box_data.map(|(box_data, _)| box_data),
        },
        des,
    ))
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &StructData<'vir, (RustTyDatas, PureTyDatas)>,
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<StructData<'vir, ImpureTyDatas>, EncodeFullError<'vir, TyImpureEnc>> {
    let (data, _, snap_expr) = ty_impure_variant("", task_key, data, deps, builder)?;

    // Ref-to-snap
    builder.mk_snap_function(Some(snap_expr));
    Ok(data)
}

pub(super) type ImpureVariant<'vir> = (
    StructData<'vir, ImpureTyDatas>,
    PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>,
    vir::ExprCSnap<'vir>,
);

pub(crate) fn ty_impure_variant<'vir>(
    prefix: &str,
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &StructData<'vir, (RustTyDatas, PureTyDatas)>,
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<ImpureVariant<'vir>, EncodeFullError<'vir, TyImpureEnc>> {
    let fields = data
        .fields
        .iter()
        .map(|f| {
            let ty = f.0.decompose(task_key.0.params);
            deps.require_dep::<TyUseImpureEnc>(ty)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // For a `Box`, its extras and the (heap-dependent) address of its dynamic
    // value field. Since the value field comes after the `Unique` field, its
    // predicate conjunct below is framed.
    let box_data = if let RustTySpecial::Box = task_key.0.special {
        Some(super::r#box::mk_impure_box_data(data, &fields, builder))
    } else {
        None
    };

    // Ref-to-Ref function for every field
    let field_accessors = data
        .fields
        .iter()
        .map(|field| TyImpureFieldData {
            ref_to_field_ref: match field.1.ref_to_field_ref {
                TyPureFieldRef::Constant(ref_to_field_ref) => ref_to_field_ref,
                TyPureFieldRef::Dynamic(_) => box_data.unwrap().1,
            },
        })
        .collect::<Vec<_>>();

    // main variant predicate
    let mut pred_name = String::new();
    if !prefix.is_empty() {
        pred_name = format!("{prefix}owned");
    }
    let pred_expr = builder.vcx.mk_conj(
        &fields
            .iter()
            .zip(&field_accessors)
            .map(|(field, TyImpureFieldData { ref_to_field_ref })| {
                field.ref_to_pred(
                    builder.vcx,
                    ref_to_field_ref(
                        ref_self,
                        builder.params.ty_exprs(),
                        builder.params.const_exprs(),
                    ),
                    None,
                )
            })
            .collect::<Vec<_>>(),
    );
    let pred_owned = builder.mk_predicate(&pred_name, Some(pred_expr));

    // Ref-to-snap
    let snap_args: Vec<&'vir vir::ExprGenData<'vir, (), !, vir::Snap>> = fields
        .iter()
        .zip(&field_accessors)
        .map(|(field, TyImpureFieldData { ref_to_field_ref })| {
            field.ref_to_snap(ref_to_field_ref(
                ref_self,
                builder.params.ty_exprs(),
                builder.params.const_exprs(),
            ))
        })
        .collect::<Vec<_>>();
    let variant_snap_expr = data.1.field_snaps_to_snap.call()(snap_args.as_slice());

    Ok((
        StructData::new(
            TyImpureStructData {
                box_data: box_data.map(|(box_data, _)| box_data),
            },
            field_accessors,
        ),
        pred_owned,
        variant_snap_expr,
    ))
}
