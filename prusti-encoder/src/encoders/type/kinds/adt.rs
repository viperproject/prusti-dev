use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, ToKnownArity};
use crate::encoders::{domain::{DomainBuilder, DomainDataEnum, DomainDataStruct, DomainDataVariant, DomainEnc, DomainEncSpecifics, FieldFunctions, FieldTy}, most_generic_ty::get_vir_base_name_kind, predicate::{PredicateBuilder, PredicateEncData, PredicateEncDataEnum, PredicateEncDataStruct, PredicateEncDataVariant, PredicateEncOutput}, rust_ty_predicates::RustTyPredicatesEnc, rust_ty_snapshots::RustTySnapshotsEnc, snapshot::SnapshotEncOutput, PredicateEnc, PredicateEncOutputRef, SnapshotEnc};

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Adt(adt, params) = ty_kind else { unreachable!(); };

    let base_name = get_vir_base_name_kind(&ty_kind, builder.vcx);
    builder.set_name(&base_name);

    let typeof_ident = builder.function("typeof", &[builder.self_type()], builder.type_type());

    deps.emit_output_ref(task_key, builder.output_ref(base_name, typeof_ident.to_known()))?;

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

    match adt.adt_kind() {
        ty::AdtKind::Struct if adt.is_box() => {
            /*
                // Box special case (this should be replaced by an
                // extern spec in the future)
                vec![FieldTy {
                    ty: enc.deps.require_ref::<GenericEnc>(())?.param_snapshot,
                    rust_ty_data: None,
                }]
            */
            todo!()
        }
        ty::AdtKind::Struct => {
            let variant = adt.non_enum_variant();
            let fields = FieldTy::mk_field_tys(builder.vcx, deps, variant, params)?;

            // constructor
            let cons_ident = builder.function(
                "cons",
                builder.vcx.alloc_slice(&fields.iter().map(|fty| fty.ty).collect::<Vec<_>>()),
                builder.self_type(),
            );

            // field accessors
            let field_reads = fields
                .iter()
                .enumerate()
                .map(|(idx, ty)| builder.function(&format!("read_{idx}"), &[builder.self_type()], ty.ty))
                .collect::<Vec<_>>();
            let field_writes = fields
                .iter()
                .enumerate()
                .map(|(idx, ty)| builder.function(&format!("write_{idx}"), &[builder.self_type(), ty.ty], builder.self_type()))
                .collect::<Vec<_>>();

            // variables for quantifiers
            let field_vars = fields
                .iter()
                .enumerate()
                .map(|(idx, ty)| builder.vcx.mk_local(&vir_format!(builder.vcx, "f{idx}"), ty.ty))
                .collect::<Vec<_>>();

            // field accessor axioms
            for idx in 0..fields.len() {
                builder.axiom(&format!("cons_read_{idx}"), vir::expr! {
                    forall ..[field_vars] ::
                        {[cons_ident](..[field_vars])}
                        ([field_reads[idx]]([cons_ident](..[field_vars]))) == ([field_vars[idx]])
                });
            }
            for write_idx in 0..fields.len() {
                for read_idx in 0..fields.len() {
                    // TODO: is the trigger here too specific? we could trigger on the read already?
                    builder.axiom(&format!("write_{write_idx}_read_{read_idx}"), if read_idx == write_idx {
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

            let field_access = field_reads.into_iter()
                .zip(field_writes)
                .map(|(read, write)| FieldFunctions {
                    read: read.to_known(),
                    write: write.to_known(),
                })
                .collect::<Vec<_>>();

            Ok(DomainEncSpecifics::StructLike(DomainDataStruct {
                field_snaps_to_snap: cons_ident,
                field_access: builder.vcx.alloc_slice(&field_access),
            }))
        }
        ty::AdtKind::Enum => {
            use prusti_rustc_interface::middle::ty::util::IntTypeExt;
            //let has_explicit = adt
            //    .variants()
            //    .iter()
            //    .any(|v| matches!(v.discr, ty::VariantDiscr::Explicit(_)));
            let discr_ty = deps
                .require_local::<RustTySnapshotsEnc>(adt.repr().discr_type().to_ty(builder.vcx.tcx()))?
                .generic_snapshot;
            let discr_prim = discr_ty.specifics.expect_primitive();

            // discriminant
            let discr_ident = builder.function(
                "discr",
                &[builder.self_type()],
                discr_ty.snapshot,
            );

            let variants = adt
                .variants()
                .iter_enumerated()
                .zip(adt.discriminants(builder.vcx.tcx()))
                .map(|((var_idx, variant), (_, discr))| {
                    let var_idx_num = var_idx.as_u32();
                    let discr = discr_ty.specifics.expect_primitive().prim_to_snap.apply(
                        builder.vcx,
                        [discr_prim.expr_from_bits(discr.ty, discr.val)],
                    );

                    // TODO: code duplication
                    let fields = FieldTy::mk_field_tys(builder.vcx, deps, variant, params)?;

                    // constructor
                    let cons_ident = builder.function(
                        &format!("cons_{var_idx_num}"),
                        builder.vcx.alloc_slice(&fields.iter().map(|fty| fty.ty).collect::<Vec<_>>()),
                        builder.self_type(),
                    );

                    // field accessors
                    let field_reads = fields
                        .iter()
                        .enumerate()
                        .map(|(idx, ty)| builder.function(&format!("read_{var_idx_num}_{idx}"), &[builder.self_type()], ty.ty))
                        .collect::<Vec<_>>();
                    let field_writes = fields
                        .iter()
                        .enumerate()
                        .map(|(idx, ty)| builder.function(&format!("write_{var_idx_num}_{idx}"), &[builder.self_type(), ty.ty], builder.self_type()))
                        .collect::<Vec<_>>();

                    // variables for quantifiers
                    let field_vars = fields
                        .iter()
                        .enumerate()
                        .map(|(idx, ty)| builder.vcx.mk_local(&vir_format!(builder.vcx, "f{idx}"), ty.ty))
                        .collect::<Vec<_>>();

                    // discriminant of constructor is known
                    builder.axiom(&format!("cons_discr_{var_idx_num}"), vir::expr! {
                        forall ..[field_vars] ::
                            {[cons_ident](..[field_vars])}
                            ([discr_ident]([cons_ident](..[field_vars]))) == ([discr])
                    });

                    // field accessor axioms
                    for idx in 0..fields.len() {
                        builder.axiom(&format!("cons_read_{var_idx_num}_{idx}"), vir::expr! {
                            forall ..[field_vars] ::
                                {[cons_ident](..[field_vars])}
                                ([field_reads[idx]]([cons_ident](..[field_vars]))) == ([field_vars[idx]])
                        });
                    }
                    for write_idx in 0..fields.len() {
                        for read_idx in 0..fields.len() {
                            // TODO: is the trigger here too specific? we could trigger on the read already?
                            builder.axiom(&format!("write_{var_idx_num}_{write_idx}_read_{read_idx}"), if read_idx == write_idx {
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

                    let field_access = field_reads.into_iter()
                        .zip(field_writes)
                        .map(|(read, write)| FieldFunctions {
                            read: read.to_known(),
                            write: write.to_known(),
                        })
                        .collect::<Vec<_>>();

                    Ok(DomainDataVariant {
                        name: variant.name,
                        vid: var_idx,
                        discr,
                        fields: DomainDataStruct {
                            field_snaps_to_snap: cons_ident,
                            field_access: builder.vcx.alloc_slice(&field_access),
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
    builder: &mut PredicateBuilder<'vir>,
) -> Result<(usize, usize), EncodeFullError<'vir, PredicateEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Adt(adt, params) = ty_kind else { unreachable!(); };

    let base_name = get_vir_base_name_kind(&ty_kind, builder.vcx);
    builder.set_name(&base_name);

    let snap_type = snap.snapshot;

    let snap_self = builder.vcx.mk_local("self", snap_type);
    let snap_self_decl = builder.vcx.mk_local_decl_local(snap_self);
    let snap_self_ex: vir::Expr = builder.vcx.mk_local_ex_local(snap_self);

    let ref_self = builder.vcx.mk_local("self", &vir::TypeData::Ref);
    let ref_self_decl = builder.vcx.mk_local_decl_local(ref_self);
    let ref_self_ex = builder.vcx.mk_local_ex_local(ref_self);

    let self_pred_ident = builder.predicate_ident(
        "owned",
        &[ref_self_decl],
    );
    let snap_func_ident = builder.function_ident(
        "snap",
        &[ref_self_decl],
        snap_type,
    );

    // unreachable (requires false) to snap (TODO: move to domain enc)
    let unr_idx = builder.functions.len();
    let unreachable_to_snap = builder.function(
        "unreachable",
        &[],
        snap_type,
        &[builder.vcx.mk_bool::<false>()],
        &[builder.vcx.mk_bool::<false>()], // TODO: is this necessary?
        None,
    );

    // assign method
    let value = builder.vcx.mk_local("value", snap_type);
    let method_assign = builder.method(
        "assign",
        &[
            ref_self_decl,
            builder.vcx.mk_local_decl_local(value),
        ],
        &[],
        &[],
        &[
            vir::expr! { [self_pred_ident](ref_self) },
            vir::expr! { ([snap_func_ident](ref_self)) == (value) },
        ],
    );

    // TODO: we don't need to know that X is specifically a struct for:
    // - p_X_unreachable
    // - p_X_snap signature (but not body!)
    // - assign_p_X

    match adt.adt_kind() {
        ty::AdtKind::Struct if adt.is_box() => {
            todo!()
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
                .map(|f| deps.require_ref::<RustTyPredicatesEnc>(f.ty(builder.vcx.tcx(), params)).unwrap())
                .collect::<Vec<_>>();

            // Ref-to-Ref function for every field
            let f0_idx = builder.functions.len();
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
            let fn_idx = builder.functions.len();

            // main predicate
            let self_pred = builder.predicate(
                "owned",
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
            let snap_idx = builder.functions.len();
            let snap_func = builder.function(
                "snap",
                &[ref_self_decl],
                snap_type,
                &[vir::expr! { acc_wildcard([self_pred](ref_self)) }],
                &[],
                Some(vir::expr! {
                    unfolding_wildcard ([self_pred](ref_self)) in ([snap_data.field_snaps_to_snap](..[snap_args]))
                }),
            );

            // lifetime projection predicates
            let lft_predicates = params.iter()
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

            deps.emit_output_ref(
                task_key,
                PredicateEncOutputRef {
                    ref_to_pred: self_pred,
                    ref_to_snap: snap_func,
                    unreachable_to_snap: unreachable_to_snap.to_known(),
                    method_assign,
                    snapshot: snap_type,
                    specifics: PredicateEncData::StructLike(PredicateEncDataStruct {
                        snap_data,
                        ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors.iter()
                            .map(|f| f.to_known())
                            .collect::<Vec<_>>()),
                    }),
                    generics: builder.vcx.alloc_slice(&snap.generics.iter().map(|g| g.decl()).collect::<Vec<_>>()),
                },
            )?;

            Ok((unr_idx, snap_idx))
        }
        ty::AdtKind::Enum => {
            let snap_data = snap.specifics.expect_enumlike().unwrap();

            // first encode the discriminant's type
            let discr_ty = ty.discriminant_ty(builder.vcx.tcx());
            let discr_ty_snap = deps.require_local::<RustTySnapshotsEnc>(discr_ty)?;
            let discr_ty_snap_prim = discr_ty_snap.generic_snapshot.specifics.expect_primitive();
            let discr_ty_out = deps.require_ref::<RustTyPredicatesEnc>(discr_ty)?;

            // Ref-to-Ref function for the discriminant field
            let fdisc_idx = builder.functions.len();
            let fdisc_func = builder.function(
                &format!("field_discr"),
                &[ref_self_decl],
                &vir::TypeData::Ref,
                &[],
                &[
                    vir::expr! { ((ref_self) == (null)) == (([builder.vcx.mk_result(&vir::TypeData::Ref)]) == (null)) },
                ],
                None,
            );

            let mut ref_to_field_refs = Vec::new();
            ref_to_field_refs.push(builder.functions[fdisc_idx]);

            let variants = adt
                .variants()
                .iter_enumerated()
                .zip(adt.discriminants(builder.vcx.tcx()))
                .zip(snap_data.variants)
                .map(|(((var_idx, variant), (_, discr)), snap_variant)| {
                    let var_idx_num = var_idx.as_u32();

                    // TODO: code duplication
                    let fields = variant
                        .fields
                        .iter()
                        .map(|f| deps.require_ref::<RustTyPredicatesEnc>(f.ty(builder.vcx.tcx(), params)).unwrap())
                        .collect::<Vec<_>>();

                    // Ref-to-Ref function for every field
                    let f0_idx = builder.functions.len();
                    let field_accessors = fields.iter()
                        .enumerate()
                        .map(|(idx, _field)| builder.function(
                            &format!("field_{var_idx_num}_{idx}"),
                            &[ref_self_decl],
                            &vir::TypeData::Ref,
                            &[],
                            &[
                                vir::expr! { ((ref_self) == (null)) == (([builder.vcx.mk_result(&vir::TypeData::Ref)]) == (null)) },
                            ],
                            None,
                        ))
                        .collect::<Vec<_>>();
                    let fn_idx = builder.functions.len();
                    ref_to_field_refs.extend(builder.functions[f0_idx..fn_idx].iter().cloned());

                    // main variant predicate
                    let variant_pred = builder.predicate(
                        &format!("owned_{var_idx_num}"),
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
                    let variant_snap_expr = vir::expr! {
                        unfolding_wildcard ([variant_pred](ref_self)) in ([snap_variant.fields.field_snaps_to_snap](..[snap_args]))
                    };
                    let variant_pred_expr = vir::expr! {
                        (([discr_ty_out.ref_to_snap(builder.vcx, fdisc_func.apply(builder.vcx, &[ref_self_ex]))])
                            == ([snap_variant.discr])) => ([variant_pred](ref_self))
                    };

                    // TODO: lifetime projection predicates

                    Ok((
                        variant_snap_expr,
                        variant_pred_expr,
                        PredicateEncDataVariant {
                            predicate: variant_pred,
                            vid: var_idx,
                            discr: snap_variant.discr,
                            fields: PredicateEncDataStruct {
                                snap_data: snap_variant.fields,
                                ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors.iter()
                                    .map(|f| f.to_known())
                                    .collect::<Vec<_>>()),
                            },
                        },
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?;

            // main predicate
            let discr_app = discr_ty_out.ref_to_snap(builder.vcx, fdisc_func.apply(builder.vcx, &[ref_self_ex]));
            let self_pred = builder.predicate(
                &format!("owned"),
                &[ref_self_decl],
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
            let snap_idx = builder.functions.len();
            let snap_func = builder.function(
                "snap",
                &[ref_self_decl],
                snap_type,
                &[vir::expr! { acc_wildcard([self_pred](ref_self)) }],
                &[],
                Some(vir::expr! {
                    unfolding_wildcard ([self_pred](ref_self)) in ([variants.iter()
                        .fold(unreachable_to_snap.apply(builder.vcx, &[]), |else_, variant| builder.vcx.mk_ternary_expr(
                            vir::expr! { ([discr_app]) == ([variant.2.discr]) },
                            variant.0,
                            else_,
                        ))])
                }),
            );

            deps.emit_output_ref(
                task_key,
                PredicateEncOutputRef {
                    ref_to_pred: self_pred,
                    ref_to_snap: snap_func,
                    unreachable_to_snap: unreachable_to_snap.to_known(),
                    method_assign,
                    snapshot: snap_type,
                    specifics: PredicateEncData::EnumLike(Some(PredicateEncDataEnum {
                        discr: fdisc_func.to_known(),
                        discr_prim: discr_ty_snap_prim,
                        //discr_bounds: (),
                        variants: builder.vcx.alloc_slice(&variants.iter().map(|v| v.2).collect::<Vec<_>>()),
                    })),
                    /*
                    specifics: PredicateEncData::StructLike(PredicateEncDataStruct {
                        snap_data,
                        ref_to_field_refs: builder.vcx.alloc_slice(&field_accessors.iter()
                            .map(|f| f.to_known())
                            .collect::<Vec<_>>()),
                    }),
                    */
                    generics: builder.vcx.alloc_slice(&snap.generics.iter().map(|g| g.decl()).collect::<Vec<_>>()),
                },
            )?;

            Ok((unr_idx, snap_idx))
        }
        ty::AdtKind::Union => todo!(),
    }
}

/*
pub(crate) fn project_to_lifetimes(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
) {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let ty::TyKind::Adt(adt, params) = ty_kind else { unreachable!(); };


}
*/
