use crate::encoders::{
    domain::{
        DomainBuilder, DomainDataEnum, DomainDataStruct, DomainDataVariant, DomainEnc,
        DomainEncOutputRef, DomainEncSpecifics, FieldTy,
    },
    lifted::ty::{EncodeGenericsAsParamTy, LiftedTyEnc},
    predicate::{
        PredicateBuilder, PredicateEncData, PredicateEncDataEnum, PredicateEncDataStruct,
        PredicateEncDataVariant,
    },
    rust_ty_predicates::RustTyPredicatesEnc,
    rust_ty_snapshots::RustTySnapshotsEnc,
    snapshot::SnapshotEncOutput,
    PredicateEnc,
};
use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::ToKnownArity;

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    output_ref: &DomainEncOutputRef<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Adt(adt, params) = ty_kind else {
        unreachable!();
    };

    let generics = params
        .iter()
        .flat_map(ty::GenericArg::as_type)
        .map(|ty| {
            deps.require_local::<LiftedTyEnc<EncodeGenericsAsParamTy>>(ty)
                .unwrap()
                .expect_generic()
        })
        .collect::<Vec<_>>();

    match adt.adt_kind() {
        ty::AdtKind::Struct if adt.is_box() => {
            /*
            let (field_snaps_to_snap, field_access, _) = super::structlike::domain("", &[FieldTy {
                rust_ty: generics[0].to_ty(builder.vcx.tcx()),
                ty: deps.require_ref::<GenericEnc>(())?.param_snapshot,
                rust_ty_data: None,
            }], task_key, output_ref, &generics, deps, builder)?;
            */
            let (field_snaps_to_snap, field_access, _) = super::structlike::domain(
                "",
                &[FieldTy::from_ty(
                    builder.vcx,
                    deps,
                    generics[0].to_ty(builder.vcx.tcx()),
                )?],
                task_key,
                output_ref,
                &generics,
                deps,
                builder,
            )?;

            Ok(DomainEncSpecifics::StructLike(DomainDataStruct {
                field_snaps_to_snap,
                field_access,
            }))
        }
        ty::AdtKind::Struct => {
            let variant = adt.non_enum_variant();
            let fields = FieldTy::mk_field_tys(builder.vcx, deps, variant, params)?;

            let (field_snaps_to_snap, field_access, _) = super::structlike::domain(
                "", &fields, task_key, output_ref, &generics, deps, builder,
            )?;

            Ok(DomainEncSpecifics::StructLike(DomainDataStruct {
                field_snaps_to_snap,
                field_access,
            }))
        }
        ty::AdtKind::Enum => {
            use prusti_rustc_interface::middle::ty::util::IntTypeExt;
            //let has_explicit = adt
            //    .variants()
            //    .iter()
            //    .any(|v| matches!(v.discr, ty::VariantDiscr::Explicit(_)));
            let discr_ty = deps
                .require_local::<RustTySnapshotsEnc>(
                    adt.repr().discr_type().to_ty(builder.vcx.tcx()),
                )?
                .generic_snapshot;
            let discr_prim = discr_ty.specifics.expect_primitive();

            // discriminant
            let discr_ident = builder.function("discr", &[builder.self_type()], discr_ty.snapshot);

            let variants =
                adt.variants()
                    .iter_enumerated()
                    .zip(adt.discriminants(builder.vcx.tcx()))
                    .map(|((var_idx, variant), (_, discr))| {
                        let var_idx_num = var_idx.as_u32();
                        let discr = discr_ty.specifics.expect_primitive().prim_to_snap.apply(
                            builder.vcx,
                            [discr_prim.expr_from_bits(discr.ty, discr.val)],
                        );

                        let fields = FieldTy::mk_field_tys(builder.vcx, deps, variant, params)?;

                        let (field_snaps_to_snap, field_access, field_vars) =
                            super::structlike::domain(
                                &format!("{var_idx_num}_"),
                                &fields,
                                task_key,
                                output_ref,
                                &generics,
                                deps,
                                builder,
                            )?;

                        // discriminant of constructor is known
                        builder.axiom(&format!("{var_idx_num}_cons_discr"), vir::expr! {
                        forall ..[field_vars] ::
                            {[field_snaps_to_snap](..[field_vars])}
                            ([discr_ident]([field_snaps_to_snap](..[field_vars]))) == ([discr])
                    });

                        Ok(DomainDataVariant {
                            name: variant.name,
                            vid: var_idx,
                            discr,
                            fields: DomainDataStruct {
                                field_snaps_to_snap,
                                field_access,
                            },
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;

            // discriminant can only have the selected values
            builder.axiom("discr_values", vir::expr! {
                forall s: [builder.self_type()] :: {[discr_ident](s)} [builder.vcx.mk_disj(&variants.iter()
                    .map(|variant| vir::expr! {
                        ([discr_ident](s)) == ([variant.discr])
                    })
                    .collect::<Vec<_>>())]
            });

            Ok(DomainEncSpecifics::EnumLike(Some(DomainDataEnum {
                discr_ty: discr_ty.snapshot,
                discr_prim,
                //pub discr_bounds: DiscrBounds<'vir>,
                snap_to_discr_snap: discr_ident.to_known(),
                variants: builder.vcx.alloc_slice(&variants), //pub variants: &'vir [DomainDataVariant<'vir>],
            })))

            /*
            let variants = if variants.is_empty() {
                None
            } else {
                let has_explicit = adt
                    .variants()
                    .iter()
                    .any(|v| matches!(v.discr, ty::VariantDiscr::Explicit(_)));
                let discr_ty = adt.repr().discr_type().to_ty(vcx.tcx());
                let discr_ty = enc
                    .deps
                    .require_local::<RustTySnapshotsEnc>(discr_ty)?
                    .generic_snapshot;
                Some(VariantData {
                    discr_ty: discr_ty.snapshot,
                    discr_prim: discr_ty.specifics.expect_primitive(),
                    has_explicit,
                    variants,
                })
            };
            let specifics = enc.mk_enum_specifics(variants);
            Ok((Some(enc.finalize(task_key)), specifics))
            */
        }
        ty::AdtKind::Union => todo!(),
    }
}

pub(crate) fn predicate<'vir>(
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: SnapshotEncOutput<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDecl<'vir>],
    generic_exprs: &[vir::Expr<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (
        PredicateEncData<'vir>,
        Option<vir::ExprGen<'vir, vir::Expr<'vir>, vir::ExprKind<'vir>>>,
    ),
    EncodeFullError<'vir, PredicateEnc>,
> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Adt(adt, params) = ty_kind else {
        unreachable!();
    };

    let snap_type = snap.snapshot;

    let snap_self = builder.vcx.mk_local("self", snap_type);
    let snap_self_decl = builder.vcx.mk_local_decl_local(snap_self);
    let snap_self_ex: vir::Expr = builder.vcx.mk_local_ex_local(snap_self);

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    match adt.adt_kind() {
        ty::AdtKind::Struct if adt.is_box() => {
            let snap_data = snap.specifics.expect_structlike();

            //let fields = variant
            //    .fields
            //    .iter()
            //    .map(|f| deps.require_ref::<RustTyPredicatesEnc>(f.ty(builder.vcx.tcx(), params)).unwrap())
            //    .collect::<Vec<_>>();

            let (field_accessors, self_pred, snap_expr) = super::structlike::predicate(
                "",
                &[deps.require_ref::<RustTyPredicatesEnc>(params[0].expect_ty())?],
                task_key,
                &snap,
                snap_data.field_snaps_to_snap,
                deps,
                generic_decls,
                generic_exprs,
                builder,
            )?;

            // Ref-to-snap
            builder.function_snap = Some(
                builder
                    .mk_function(
                        "snap",
                        &[ref_self_decl]
                            .into_iter()
                            .chain(generic_decls.iter().cloned())
                            .collect::<Vec<_>>(),
                        snap_type,
                        &[vir::expr! { acc_wildcard([self_pred](ref_self, ..[generic_exprs])) }],
                        &[],
                        Some(snap_expr),
                    )
                    .1,
            );

            Ok((
                PredicateEncData::StructLike(PredicateEncDataStruct {
                    snap_data,
                    ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors),
                }),
                None,
            ))
        }
        ty::AdtKind::Struct => {
            let snap_data = snap.specifics.expect_structlike();

            // for struct X<'a, 'b> {
            //   o: i32,
            //   a: &'a mut i32,
            //   b: &'b mut i32,
            // }
            // we should emit:
            // fields accessors
            // - function p_X_field_0(self: Ref): Ref
            // - function p_X_field_1(self: Ref): Ref
            // - function p_X_field_2(self: Ref): Ref
            // predicates
            // - p_X(self: Ref) { // owned fields
            //     p_Int_i32(p_X_field_0(self))
            //     && p_Ref_mutable(p_X_field_1(self), s_Int_i32_type())
            //     && p_Ref_mutable(p_X_field_2(self), s_Int_i32_type())
            //   }
            // - p_X_lft0(self: s_X) { // projection through 'a
            //     p_Int_i32(s_Ref_deref(s_X_read_1(self)))
            //   }
            // - p_X_lft0(self: s_X) { // projection through 'a
            //     p_Int_i32(s_Ref_deref(s_X_read_2(self)))
            //   }
            // functions
            // - function p_X_unreachable(): s_X // for now; should be moved to domain encoder
            // - function p_X_snap(self: Ref): s_X { .. }
            // methods
            // - method assign_p_X(self: Ref, value: s_X)

            let variant = adt.non_enum_variant();
            let fields = variant
                .fields
                .iter()
                .map(|f| {
                    deps.require_ref::<RustTyPredicatesEnc>(f.ty(builder.vcx.tcx(), params))
                        .unwrap()
                })
                .collect::<Vec<_>>();

            let (field_accessors, self_pred, snap_expr) = super::structlike::predicate(
                "",
                &fields,
                task_key,
                &snap,
                snap_data.field_snaps_to_snap,
                deps,
                generic_decls,
                generic_exprs,
                builder,
            )?;

            // Ref-to-snap
            builder.function_snap = Some(
                builder
                    .mk_function(
                        "snap",
                        &[ref_self_decl]
                            .into_iter()
                            .chain(generic_decls.iter().cloned())
                            .collect::<Vec<_>>(),
                        snap_type,
                        &[vir::expr! { acc_wildcard([self_pred](ref_self, ..[generic_exprs])) }],
                        &[],
                        Some(snap_expr),
                    )
                    .1,
            );

            /*
            // lifetime projection predicates
            let _lft_predicates = params.iter()
                .enumerate()
                .flat_map(|(reg_idx, arg)| Some((reg_idx, arg.as_region()?)))
                .map(|(reg_idx, reg)| builder.predicate(
                        &format!("lft_{reg_idx}"),
                        &[snap_self_decl],
                        Some(builder.vcx.mk_conj(&fields.iter()
                            .zip(&variant.fields)
                            .enumerate()
                            .filter_map(|(field_idx, (field, rust_field))| match rust_field.ty(builder.vcx.tcx(), params).kind() {
                                ty::TyKind::Ref(field_reg, inner_ty, ty::Mutability::Mut) => {
                                    if *field_reg != reg {
                                        return None;
                                    }
                                    let inner_ty_enc = deps.require_ref::<RustTyPredicatesEnc>(*inner_ty).unwrap();
                                    Some(inner_ty_enc.ref_to_pred(
                                        builder.vcx,
                                        field.generic_predicate.expect_ref().snap_data.deref_access.apply(builder.vcx, [
                                            snap_data.field_access[field_idx].read.apply(builder.vcx, [snap_self_ex]),
                                        ]),
                                        None,
                                    ))
                                }
                                _ => None,
                            })
                            .collect::<Vec<_>>()))
                    ))
                .collect::<Vec<_>>();
            */

            Ok((
                PredicateEncData::StructLike(PredicateEncDataStruct {
                    snap_data,
                    ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors),
                }),
                None,
            ))
        }
        ty::AdtKind::Enum => {
            let snap_data = snap.specifics.expect_enumlike().unwrap();

            // first encode the discriminant's type
            let discr_ty = ty.discriminant_ty(builder.vcx.tcx());
            let discr_ty_snap = deps.require_local::<RustTySnapshotsEnc>(discr_ty)?;
            let discr_ty_snap_prim = discr_ty_snap.generic_snapshot.specifics.expect_primitive();
            let discr_ty_out = deps.require_ref::<RustTyPredicatesEnc>(discr_ty)?;

            // Ref-to-Ref function for the discriminant field
            let fdisc_func = builder.function(
                "field_discr",
                &[ref_self_decl],
                &vir::TypeData::Ref,
                &[],
                &[
                    vir::expr! { ((ref_self) == (null)) == (([builder.vcx.mk_result(&vir::TypeData::Ref)]) == (null)) },
                ],
                None,
            );

            let variants = adt
                .variants()
                .iter_enumerated()
                .zip(snap_data.variants)
                .map(|((var_idx, variant), snap_variant)| {
                    let var_idx_num = var_idx.as_u32();

                    let fields = variant
                        .fields
                        .iter()
                        .map(|f| deps.require_ref::<RustTyPredicatesEnc>(f.ty(builder.vcx.tcx(), params)).unwrap())
                        .collect::<Vec<_>>();

                    let (
                        field_accessors,
                        variant_pred,
                        variant_snap_expr,
                    ) = super::structlike::predicate(
                        &format!("{var_idx_num}_"),
                        &fields,
                        task_key,
                        &snap,
                        snap_variant.fields.field_snaps_to_snap,
                        deps,
                        generic_decls,
                        generic_exprs,
                        builder,
                    )?;

                    let variant_pred_expr = vir::expr! {
                        (([discr_ty_out.ref_to_snap(builder.vcx, fdisc_func.apply(builder.vcx, &[ref_self_ex]))])
                            == ([snap_variant.discr])) => ([variant_pred](ref_self, ..[generic_exprs]))
                    };

                    Ok((
                        variant_snap_expr,
                        variant_pred_expr,
                        PredicateEncDataVariant {
                            predicate: variant_pred,
                            vid: var_idx,
                            discr: snap_variant.discr,
                            fields: PredicateEncDataStruct {
                                snap_data: snap_variant.fields,
                                ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors),
                            },
                        },
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?;

            // main predicate
            let discr_app = discr_ty_out
                .ref_to_snap(builder.vcx, fdisc_func.apply(builder.vcx, &[ref_self_ex]));
            let self_pred = builder.predicate(
                "",
                &[ref_self_decl].into_iter()
                    .chain(generic_decls.iter().cloned())
                    .collect::<Vec<_>>(),
                Some(vir::expr! {
                    ([discr_ty_out.ref_to_pred(builder.vcx, fdisc_func.apply(builder.vcx, &[ref_self_ex]), None)])
                    && (([builder.vcx.mk_disj(&variants.iter()
                        .map(|variant| vir::expr! { ([discr_app]) == ([variant.2.discr]) })
                        .collect::<Vec<_>>())])
                    && ([builder.vcx.mk_conj(&variants.iter()
                        .map(|v| v.1)
                        .collect::<Vec<_>>())]))
                }),
            );

            // Ref-to-snap
            builder.function_snap = Some(builder.mk_function(
                "snap",
                &[ref_self_decl].into_iter()
                    .chain(generic_decls.iter().cloned())
                    .collect::<Vec<_>>(),
                snap_type,
                &[vir::expr! { acc_wildcard([self_pred](ref_self, ..[generic_exprs])) }],
                &[],
                Some(vir::expr! {
                    unfolding_wildcard ([self_pred](ref_self, ..[generic_exprs])) in ([variants.iter()
                        .fold(builder.unreachable_to_snap.unwrap().0.apply(builder.vcx, []), |else_, variant| builder.vcx.mk_ternary_expr(
                            vir::expr! { ([discr_app]) == ([variant.2.discr]) },
                            variant.0,
                            else_,
                        ))])
                }),
            ).1);

            Ok((
                PredicateEncData::EnumLike(Some(PredicateEncDataEnum {
                    discr: fdisc_func.to_known(),
                    discr_prim: discr_ty_snap_prim,
                    //discr_bounds: (),
                    variants: builder
                        .vcx
                        .alloc_slice(&variants.iter().map(|v| v.2).collect::<Vec<_>>()),
                })),
                None,
            ))
        }
        ty::AdtKind::Union => todo!(),
    }
}
