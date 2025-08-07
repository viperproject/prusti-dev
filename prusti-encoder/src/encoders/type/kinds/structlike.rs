use crate::encoders::{
    domain::{AdtBuilder, FieldTy},
    predicate::PredicateBuilder,
    rust_ty_predicates::RustTyPredicatesEncOutputRef,
    snapshot::SnapshotEncOutput, PredicateEnc,
};
use prusti_rustc_interface::middle::ty::ParamTy;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, CastType, FunctionIdn, HasType, PredicateIdn};

pub fn domain<'vir>(
    prefix: &str,
    fields: &[FieldTy<'vir>],
    builder: &mut AdtBuilder<'vir>,
    discr: Option<vir::ExprCSnap<'vir>>,
) -> (
    FunctionIdn<'vir, vir::ManySnap, vir::CSnap>,
    &'vir [vir::AdtDestructor<'vir, vir::CSnap, vir::Snap>],
) {
    let field_tys = builder.vcx.alloc_slice(&fields.iter().map(|f| f.ty).collect::<Vec<_>>());
    let (cons, des) = builder.constructor(prefix, field_tys, discr);
    (cons, builder.vcx.alloc_slice(&des).downcast_ty())
}

pub(crate) fn predicate<'vir>(
    prefix: &str,
    fields: &[RustTyPredicatesEncOutputRef<'vir>],
    _task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    _snap: &SnapshotEncOutput<'vir>,
    variant_field_snaps_to_snap: FunctionIdn<'vir, vir::ManySnap, vir::CSnap>,
    _deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDeclTyVal<'vir>],
    generic_exprs: &[vir::ExprTyVal<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (
        Vec<FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Ref>>,
        PredicateIdn<'vir, (vir::Ref, vir::ManyTyVal)>,
        vir::ExprCSnap<'vir>,
    ),
    EncodeFullError<'vir, PredicateEnc>,
> {
    /*
        let snap_data = snap.specifics.expect_structlike();
        let fields = variant
        .fields
        .iter()
        .map(|f| deps.require_ref::<RustTyPredicatesEnc>(f.ty(builder.vcx.tcx(), params)).unwrap())
        .collect::<Vec<_>>();
    */

    let ref_self = builder.vcx.mk_local("self", vir::TYPE_REF);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let generic_decls_tys = builder.vcx.alloc_slice(
        generic_decls
            .iter()
            .copied()
            .map(vir::LocalDeclData::ty)
            .collect::<Vec<_>>()
            .as_slice(),
    );
    // Ref-to-Ref function for every field
    let field_accessors: Vec<FunctionIdn<'vir, (vir::Ref, vir::ManyTyVal), vir::Ref>> = fields
        .iter()
        .enumerate()
        .map(|(idx, _field)| {
            builder.function::<(vir::Ref, vir::ManyTyVal), vir::Ref>(
                &format!("{prefix}field_{idx}"),
                (ref_self_decl.ty(), generic_decls_tys),
                vir::TYPE_REF,
                (ref_self_decl, generic_decls),
                &[], // TODO: should have a read permission here!
                &[vir::expr! { ((ref_self) == (null)) == ((result: Ref) == (null)) }],
                None,
            )
        })
        .collect::<Vec<_>>();

    // main variant predicate
    let mut pred_name = String::new();
    if !prefix.is_empty() {
        pred_name = format!("{prefix}owned");
    }
    let pred_owned = builder.predicate::<(vir::Ref, vir::ManyTyVal)>(
        &pred_name,
        (ref_self_decl.ty(), generic_decls_tys),
        (ref_self_decl, generic_decls),
        Some(
            builder.vcx.mk_conj(
                &fields
                    .iter()
                    .zip(&field_accessors)
                    .map(|(field, accessor)| {
                        field.ref_to_pred(builder.vcx, accessor(ref_self_ex, &generic_exprs), None)
                    })
                    .collect::<Vec<_>>(),
            ),
        ),
    );

    // Ref-to-snap
    let snap_args = fields
        .iter()
        .zip(&field_accessors)
        .map(|(field, accessor)| {
            field.ref_to_snap(builder.vcx, accessor(ref_self_ex, &generic_exprs))
        })
        .collect::<Vec<_>>();
    let variant_snap_expr = vir::expr! {
        unfolding ([pred_owned](ref_self, ..[generic_exprs])) in ([variant_field_snaps_to_snap](..[snap_args.as_slice()]))
    };
    /*
    let pred_owned_expr = vir::expr! {
        (([discr_ty_out.ref_to_snap(builder.vcx, fdisc_func.apply(builder.vcx, &[ref_self_ex]))])
            == ([snap_variant.discr])) => ([pred_owned](ref_self))
    };
    */

    /*
    let variant = adt.non_enum_variant();
    let fields = variant
        .fields
        .iter()
        .map(|f| deps.require_ref::<RustTyPredicatesEnc>(f.ty(builder.vcx.tcx(), params)).unwrap())
        .collect::<Vec<_>>();

    // Ref-to-Ref function for every field
    let field_accessors = fields.iter()
        .enumerate()
        .map(|(idx, _field)| builder.function(
            &format!("field_{idx}"),
            &[ref_self_decl],
            &vir::TypeData::Ref,
            &[],
            &[
                vir::expr! { ((ref_self) == (null)) == (([builder.vcx.mk_result(&vir::TypeData::Ref)]) == (null)) },
            ],
            None,
        ))
        .collect::<Vec<_>>();

    // main predicate
    let self_pred = builder.predicate(
        "",
        &[ref_self_decl],
        Some(builder.vcx.mk_conj(&fields.iter()
            .zip(&field_accessors)
            .map(|(field, accessor)| field.ref_to_pred(builder.vcx, accessor.apply(builder.vcx, &[ref_self_ex]), None))
            .collect::<Vec<_>>())),
    );

    // Ref-to-snap
    let snap_args = fields.iter()
        .zip(&field_accessors)
        .map(|(field, accessor)| field.ref_to_snap(builder.vcx, accessor.apply(builder.vcx, &[ref_self_ex])))
        .collect::<Vec<_>>();
    builder.function_snap = Some(builder.mk_function(
        "snap",
        &[ref_self_decl],
        snap_type,
        &[vir::expr! { acc([self_pred](ref_self)) }],
        &[],
        Some(vir::expr! {
            unfolding ([self_pred](ref_self)) in ([snap_data.field_snaps_to_snap](..[snap_args]))
        }),
    ).1);

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

    Ok(PredicateEncData::StructLike(PredicateEncDataStruct {
        snap_data,
        ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors.iter()
            .map(|f| f)
            .collect::<Vec<_>>()),
    }))
    */
    Ok((field_accessors, pred_owned, variant_snap_expr))
}
