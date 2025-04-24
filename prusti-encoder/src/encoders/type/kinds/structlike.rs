use crate::encoders::{
    domain::{DomainBuilder, DomainEnc, DomainEncOutputRef, FieldFunctions, FieldTy},
    lifted::ty_constructor::TyConstructorEnc,
    predicate::PredicateBuilder,
    rust_ty_predicates::RustTyPredicatesEncOutputRef,
    snapshot::SnapshotEncOutput,
    GenericEnc, PredicateEnc,
};
use prusti_rustc_interface::middle::ty::{ParamTy, TyKind};
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, FunctionIdent, PredicateIdent, ToKnownArity, UnknownArity};

pub fn domain<'vir>(
    prefix: &str,
    fields: &[FieldTy<'vir>],
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    output_ref: &DomainEncOutputRef<'vir>,
    generics: &[ParamTy],
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<
    (
        FunctionIdent<'vir, UnknownArity<'vir>>,
        &'vir [FieldFunctions<'vir>],
        Vec<vir::Local<'vir>>,
    ),
    EncodeFullError<'vir, DomainEnc>,
> {
    // constructor
    let cons_ident = builder.function(
        &format!("{prefix}cons"),
        builder
            .vcx
            .alloc_slice(&fields.iter().map(|fty| fty.ty).collect::<Vec<_>>()),
        builder.self_type(),
    );

    // field accessors
    let field_reads = fields
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder.function(
                &format!("{prefix}read_{idx}"),
                &[builder.self_type()],
                ty.ty,
            )
        })
        .collect::<Vec<_>>();
    let field_writes = fields
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder.function(
                &format!("{prefix}write_{idx}"),
                &[builder.self_type(), ty.ty],
                builder.self_type(),
            )
        })
        .collect::<Vec<_>>();

    // variables for quantifiers
    let field_vars = fields
        .iter()
        .enumerate()
        .map(|(idx, ty)| {
            builder
                .vcx
                .mk_local(vir_format!(builder.vcx, "f{idx}"), ty.ty)
        })
        .collect::<Vec<_>>();

    // TODO: typeof and read_type axioms
    /*
    // for struct U<T> { x: T, y: i32 }
    // this one forwards the generic
    axiom ax_s_U_read_0_type {
        forall self: s_U :: {s_U_read_0(self)} (typ(s_U_read_0(self))) == (s_U_typaram_T(typeof_s_U(self)))
    }
    // this one seems less useful: this could be an axiom over s_Int_i32_typeof generally?
    axiom ax_s_U_read_1_type {
        forall self: s_U :: {s_U_read_1(self)} (s_Int_i32_typeof(s_U_read_1(self))) == (s_Int_i32_type())
    }
    axiom ax_typeof_s_U {
        forall self: s_U :: {s_U_typaram_T(typeof_s_U(self))} (typeof_s_U(self)) == (s_U_type(s_U_typaram_T(typeof_s_U(self))))
    }
    */

    if prefix.is_empty() {
        // TODO: this ensures that we only produce one axiom for enums, but the
        //   check based on prefix is not very clean
        let ty_cons = deps.require_ref::<TyConstructorEnc>(task_key)?;
        builder.axiom("typeof", vir::expr! {
            forall s: [builder.self_type()] ::
                {[output_ref.typeof_function](s)}
                ([output_ref.typeof_function](s)) == ([ty_cons.ty_constructor](..[generics.iter()
                    .enumerate()
                    .map(|(param_idx, _)| {
                        output_ref.ty_param_accessors[param_idx].apply(builder.vcx, [output_ref.typeof_function.apply(builder.vcx, [s])])
                    })
                    .collect::<Vec<_>>()]))
        });
    }

    // field accessor axioms
    let generic_enc = deps.require_ref::<GenericEnc>(())?;
    for idx in 0..fields.len() {
        builder.axiom(
            &format!("{prefix}cons_read_{idx}"),
            vir::expr! {
                forall ..[field_vars] ::
                    {[cons_ident](..[field_vars])}
                    ([field_reads[idx]]([cons_ident](..[field_vars]))) == ([field_vars[idx]])
            },
        );
        if let TyKind::Param(p) = fields[idx].rust_ty.kind() {
            // TODO: this only handles top-level generics
            let param_idx = p.index as usize;
            builder.axiom(&format!("{prefix}type_read_{idx}"), vir::expr! {
                forall s: [builder.self_type()] ::
                    {[field_reads[idx]](s)}
                    ([generic_enc.param_type_function]([field_reads[idx]](s))) == ([output_ref.ty_param_accessors[param_idx]]([output_ref.typeof_function](s)))
            });
        }
    }
    for write_idx in 0..fields.len() {
        for read_idx in 0..fields.len() {
            // TODO: is the trigger here too specific? we could trigger on the read already?
            builder.axiom(&format!("{prefix}write_{write_idx}_read_{read_idx}"), if read_idx == write_idx {
                vir::expr! {
                    forall s: [builder.self_type()], value: [fields[write_idx].ty] ::
                        {[field_reads[read_idx]]([field_writes[write_idx]](s, value))}
                        ([field_reads[read_idx]]([field_writes[write_idx]](s, value))) == (value)
                }
            } else {
                vir::expr! {
                    forall s: [builder.self_type()], value: [fields[write_idx].ty] ::
                        {[field_reads[read_idx]]([field_writes[write_idx]](s, value))}
                        ([field_reads[read_idx]]([field_writes[write_idx]](s, value))) == ([field_reads[read_idx]](s))
                }
            });
        }
    }

    let field_access = field_reads
        .into_iter()
        .zip(field_writes)
        .map(|(read, write)| FieldFunctions {
            read: read.to_known(),
            write: write.to_known(),
        })
        .collect::<Vec<_>>();

    Ok((
        cons_ident,
        builder.vcx.alloc_slice(&field_access),
        field_vars,
    ))
}

pub(crate) fn predicate<'vir>(
    prefix: &str,
    fields: &[RustTyPredicatesEncOutputRef<'vir>],
    task_key: <PredicateEnc as TaskEncoder>::TaskKey<'vir>,
    snap: &SnapshotEncOutput<'vir>,
    variant_field_snaps_to_snap: FunctionIdent<'vir, UnknownArity<'vir>>,
    deps: &mut TaskEncoderDependencies<'vir, PredicateEnc>,
    generic_decls: &[vir::LocalDecl<'vir>],
    generic_exprs: &[vir::Expr<'vir>],
    builder: &mut PredicateBuilder<'vir>,
) -> Result<
    (
        Vec<FunctionIdent<'vir, UnknownArity<'vir>>>,
        PredicateIdent<'vir, UnknownArity<'vir>>,
        vir::Expr<'vir>,
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

    let snap_type = snap.snapshot;

    let snap_self = builder.vcx.mk_local("self", snap_type);
    let snap_self_decl = builder.vcx.mk_local_decl_local(snap_self);
    let snap_self_ex: vir::Expr = builder.vcx.mk_local_ex_local(snap_self);

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    // Ref-to-Ref function for every field
    let field_accessors = fields.iter()
        .enumerate()
        .map(|(idx, _field)| builder.function(
            &format!("{prefix}field_{idx}"),
            &[ref_self_decl].into_iter()
                .chain(generic_decls.iter().cloned())
                .collect::<Vec<_>>(),
            &vir::TypeData::Ref,
            &[], // TODO: should have a read permission here!
            &[
                vir::expr! { ((ref_self) == (null)) == (([builder.vcx.mk_result(&vir::TypeData::Ref)]) == (null)) },
            ],
            None,
        ))
        .collect::<Vec<_>>();

    // main variant predicate
    let mut pred_name = String::new();
    if !prefix.is_empty() {
        pred_name = format!("{prefix}owned");
    }
    let pred_owned = builder.predicate(
        &pred_name,
        &[ref_self_decl]
            .into_iter()
            .chain(generic_decls.iter().cloned())
            .collect::<Vec<_>>(),
        Some(
            builder.vcx.mk_conj(
                &fields
                    .iter()
                    .zip(&field_accessors)
                    .map(|(field, accessor)| {
                        field.ref_to_pred(
                            builder.vcx,
                            accessor.apply(
                                builder.vcx,
                                &[ref_self_ex]
                                    .into_iter()
                                    .chain(generic_exprs.iter().cloned())
                                    .collect::<Vec<_>>(),
                            ),
                            None,
                        )
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
            field.ref_to_snap(
                builder.vcx,
                accessor.apply(
                    builder.vcx,
                    &[ref_self_ex]
                        .into_iter()
                        .chain(generic_exprs.iter().cloned())
                        .collect::<Vec<_>>(),
                ),
            )
        })
        .collect::<Vec<_>>();
    let variant_snap_expr = vir::expr! {
        unfolding_wildcard ([pred_owned](ref_self, ..[generic_exprs])) in ([variant_field_snaps_to_snap](..[snap_args]))
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
        &[vir::expr! { acc_wildcard([self_pred](ref_self)) }],
        &[],
        Some(vir::expr! {
            unfolding_wildcard ([self_pred](ref_self)) in ([snap_data.field_snaps_to_snap](..[snap_args]))
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
            .map(|f| f.to_known())
            .collect::<Vec<_>>()),
    }))
    */
    Ok((field_accessors, pred_owned, variant_snap_expr))
}
