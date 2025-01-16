use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies};
use vir::{vir_format, ToKnownArity};
use crate::encoders::{domain::{DomainBuilder, DomainDataStruct, DomainEnc, DomainEncSpecifics, FieldFunctions, FieldTy}, most_generic_ty::get_vir_base_name_kind};

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
            todo!()
            /*
            let variants: Vec<_> = adt
                .discriminants(vcx.tcx())
                .map(|(v, d)| {
                    let variant = adt.variant(v);
                    let field_tys = enc.mk_field_tys(variant, params)?;
                    Ok((variant.name, v, field_tys, d))
                })
                .collect::<Result<Vec<_>, _>>()?;
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
