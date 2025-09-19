use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::CastType;

use crate::encoders::{
    TyUseImpureEnc,
    ty::{
        RustTyDatas, RustTyDecomposition,
        data::{EnumData, TyData, VariantData},
        impure::{
            ImpureTyDatas, PredicateBuilder, TyImpureEnc, TyImpureEnumData, TyImpureVariantData,
        },
        pure::{AdtBuilder, PureTyDatas, TyPureEnc, TyPureEnumData, TyPureVariantData},
    },
};

pub(crate) fn ty_pure<'vir>(
    task_key: &TyData<'vir, RustTyDatas>,
    data: &EnumData<'vir, RustTyDatas>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut AdtBuilder<'vir>,
) -> Result<EnumData<'vir, PureTyDatas>, EncodeFullError<'vir, TyPureEnc>> {
    let discr_ty =
        deps.require_dep::<TyPureEnc>(RustTyDecomposition::from_prim_ty(data.discr).ty)?;
    let discr_prim = discr_ty.expect_primitive();
    let discr_ty = (discr_ty.domain)().downcast_ty();

    let variants = data
        .variants
        .iter()
        .map(|variant| {
            let var_idx_num = variant.vid.as_u32();
            let discr =
                (discr_prim.prim_to_snap)(discr_prim.expr_from_bits(data.discr, variant.discr_val));

            let specifics = super::structlike::ty_pure_variant(
                &format!("{var_idx_num}_"),
                Some(discr),
                task_key,
                &variant.inner,
                deps,
                builder,
            )?;

            Ok(VariantData::new(TyPureVariantData { discr }, specifics))
        })
        .collect::<Result<Vec<_>, _>>()?;

    // discriminant can only have the selected values
    let snap_to_discr_snap = builder.build_discr_fn(discr_ty);

    Ok(EnumData::new(
        TyPureEnumData {
            discr_ty,
            discr_prim: *discr_prim,
            snap_to_discr_snap,
        },
        variants,
    ))
}

pub(crate) fn ty_impure<'vir>(
    task_key: &TyData<'vir, (RustTyDatas, PureTyDatas)>,
    data: &EnumData<'vir, (RustTyDatas, PureTyDatas)>,
    deps: &mut TaskEncoderDependencies<'vir, TyImpureEnc>,
    builder: &mut PredicateBuilder<'vir>,
) -> Result<EnumData<'vir, ImpureTyDatas>, EncodeFullError<'vir, TyImpureEnc>> {
    let ref_self_decl = builder.ref_self_decl();
    let ref_self = builder.vcx.mk_local_ex(ref_self_decl);

    // first encode the discriminant's type
    let task = RustTyDecomposition::from_prim_ty(data.0.discr);
    let discr_ty_impure = deps.require_dep::<TyUseImpureEnc>(task)?;

    // Ref-to-Ref function for the discriminant field
    let fdisc_func = builder.function(
        "field_discr",
        ref_self_decl.ty,
        vir::TYPE_REF,
        (ref_self_decl,),
        &[],
        &[vir::expr! { ((ref_self) == (null)) == ((result: Ref) == (null)) }],
        None,
    );
    let ref_disc = fdisc_func(ref_self);
    let snap_disc = discr_ty_impure.ref_to_snap(ref_disc).downcast_ty();

    let variants = data
        .variants
        .iter()
        .map(|variant| {
            let var_idx_num = variant.0.vid.as_u32();

            let (
                inner,
                variant_pred,
                variant_snap_expr,
            ) = super::structlike::ty_impure_variant(
                &format!("{var_idx_num}_"),
                task_key,
                &variant.inner,
                deps,
                builder,
            )?;

            let variant_pred_expr = vir::expr! {
                (([snap_disc])
                    == ([variant.1.discr])) ==> ([variant_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]]))
            };

            Ok((
                variant_snap_expr,
                variant_pred_expr,
                variant.1.discr,
                VariantData::new(TyImpureVariantData {
                    predicate: variant_pred,
                }, inner)
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;

    // main predicate
    let variant_predicate = discr_ty_impure.ref_to_pred(builder.vcx, ref_disc, None);
    let variant_values = builder.vcx.mk_disj(
        &variants
            .iter()
            .map(|variant| vir::expr! { ([snap_disc]) == ([variant.2]) })
            .collect::<Vec<_>>(),
    );
    let variant_predicates = builder
        .vcx
        .mk_conj(&variants.iter().map(|v| v.1).collect::<Vec<_>>());
    let self_pred = builder
        .inner
        .predicate::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap)>(
            "",
            (
                ref_self_decl.ty,
                builder.params.ty_args(),
                builder.params.const_args(),
            ),
            (
                ref_self_decl,
                builder.params.ty_decls(),
                builder.params.const_decls(),
            ),
            Some(vir::expr! {
                ([variant_predicate])
                && (([variant_values])
                && ([variant_predicates]))
            }),
        );

    // Ref-to-snap
    builder.function_snap = Some(builder.mk_function::<(vir::Ref, vir::ManyTyVal, vir::ManyCSnap), _>(
        "snap",
        (ref_self_decl.ty,
            builder.params.ty_args(), builder.params.const_args()),
        builder.csnap_type(),
        (ref_self_decl, builder.params.ty_decls(), builder.params.const_decls()),
        &[vir::expr! { acc([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) }],
        &[],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self, [..[builder.params.ty_exprs()]], [..[builder.params.const_exprs()]])) in ([variants.iter()
                .fold((task_key.1.unreachable_to_snap)(builder.params.ty_exprs()).downcast_ty(), |else_, variant| builder.vcx.mk_ternary_expr(
                    vir::expr! { ([snap_disc]) == ([variant.2]) },
                    variant.0,
                    else_,
                ))])
        }),
    ).1);

    Ok(EnumData::new(
        TyImpureEnumData {
            discr: fdisc_func,
            discr_ty: discr_ty_impure,
        },
        variants.into_iter().map(|v| v.3).collect::<Vec<_>>(),
    ))
}
