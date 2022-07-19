use super::interface::TypeInvariantEncoderInterface;
use crate::encoder::{
    errors::EncodingResult,
    high::types::HighTypeEncoderInterface,
    mir::{
        pure::SpecificationEncoderInterface, specifications::SpecificationsInterface,
        types::MirTypeEncoderInterface,
    },
    snapshot::interface::SnapshotEncoderInterface,
    Encoder,
};
use prusti_common::{vir_expr, vir_local};
use prusti_interface::specs::typed;
use prusti_rustc_interface::{
    middle::ty::{self, layout::IntegerExt},
    target::abi::Integer,
};
use vir_crate::polymorphic::{self as vir, ExprIterator};

pub(super) fn needs_invariant_func(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::TyKind::Ref(_, ty, _) => needs_invariant_func(*ty),
        ty::TyKind::Adt(adt_def, _) if adt_def.is_box() => needs_invariant_func(ty.boxed_ty()),
        //ty::TyKind::Int(..)
        //| ty::TyKind::Uint(..)
        ty::TyKind::Tuple(..) | ty::TyKind::Closure(..) => true,
        ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() || adt_def.is_enum() => true,
        _ => false,
    }
}

fn encode_invariant_func_base<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
    body: Option<vir::Expr>,
) -> EncodingResult<vir::Function> {
    let predicate_type = encoder.encode_type(ty)?;
    let snap_type = encoder.encode_snapshot_type(ty)?;
    Ok(vir::Function {
        name: format!("invariant${}", predicate_type.name()),
        type_arguments: vec![],
        formal_args: vec![vir::LocalVar::new("self", snap_type)],
        return_type: vir::Type::Bool,
        pres: vec![],
        posts: vec![],
        body,
    })
}

pub(super) fn encode_invariant_stub<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<vir::Function> {
    encode_invariant_func_base(encoder, ty, None)
}

pub(super) fn encode_invariant_def<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> EncodingResult<vir::Function> {
    let tcx = encoder.env().tcx();

    let predicate_type = encoder.encode_type(ty)?;
    let parg_self = vir_local! {self: { predicate_type } };
    let parg_expr = vir::Expr::local(parg_self);

    let snap_type = encoder.encode_snapshot_type(ty)?;
    let arg_self = vir_local! {self: { snap_type } };
    let arg_expr = vir::Expr::local(arg_self);

    let mut conjuncts = vec![];

    match ty.kind() {
        // ty should be peeled already
        ty::TyKind::Ref(..) => unreachable!(),
        ty::TyKind::Adt(adt_def, _) if adt_def.is_box() => unreachable!(),

        // TODO(inv): incorporate integer bounds
        //ty::TyKind::Int(_)
        //| ty::TyKind::Uint(_) => { ... }
        ty::TyKind::Tuple(substs) => {
            for (field_num, field_ty) in substs.iter().enumerate() {
                let field_name = format!("tuple_{}", field_num);
                conjuncts.push(encoder.encode_invariant_func_app(
                    field_ty,
                    vir::Expr::snap_app(vir::Expr::field(
                        arg_expr.clone(),
                        encoder.encode_raw_ref_field(field_name.to_string(), field_ty)?,
                    )),
                )?);
            }
        }

        ty::TyKind::Closure(_def_id, substs) => {
            let cl_substs = substs.as_closure();
            for (field_num, field_ty) in cl_substs.upvar_tys().enumerate() {
                let field_name = format!("closure_{}", field_num);
                conjuncts.push(encoder.encode_invariant_func_app(
                    field_ty,
                    vir::Expr::snap_app(vir::Expr::field(
                        arg_expr.clone(),
                        encoder.encode_raw_ref_field(field_name.to_string(), field_ty)?,
                    )),
                )?);
            }
        }

        ty::TyKind::Adt(adt_def, substs) if adt_def.is_struct() || adt_def.is_enum() => {
            if adt_def.is_struct() {
                for field in adt_def.all_fields() {
                    let field_ty = field.ty(tcx, substs);
                    conjuncts.push(encoder.encode_invariant_func_app(
                        field_ty,
                        vir::Expr::snap_app(vir::Expr::field(
                            arg_expr.clone(),
                            encoder.encode_struct_field(&field.ident(tcx).to_string(), field_ty)?,
                        )),
                    )?);
                }
            } else if adt_def.is_enum() {
                let predicate = encoder.encode_type_predicate_def(ty)?;
                let mut variants = vec![];
                for (variant_idx, variant) in adt_def.variants().iter_enumerated() {
                    let mut fields = vec![];
                    let variant_idx: usize = variant_idx.into();
                    let field_base = match predicate {
                        vir::Predicate::Enum(ref enum_predicate) => {
                            let (_, ref variant_name, _) = enum_predicate.variants[variant_idx];
                            parg_expr
                                .clone()
                                .variant(variant_name)
                                .replace_place(&parg_expr, &arg_expr)
                        }
                        vir::Predicate::Struct(..) => arg_expr.clone(),
                        _ => unreachable!(),
                    };
                    for field in &variant.fields {
                        let field_ty = field.ty(tcx, substs);
                        let field = vir::Expr::snap_app(vir::Expr::field(
                            field_base.clone(),
                            encoder.encode_struct_field(&field.ident(tcx).to_string(), field_ty)?,
                        ));
                        fields.push(encoder.encode_invariant_func_app(field_ty, field)?);
                    }

                    let discriminant_raw = adt_def
                        .discriminant_for_variant(
                            tcx,
                            prusti_rustc_interface::target::abi::VariantIdx::from_usize(
                                variant_idx,
                            ),
                        )
                        .val;
                    let size = ty::tls::with(|tcx| {
                        Integer::from_attr(&tcx, adt_def.repr().discr_type()).size()
                    });
                    let arg_discriminant =
                        arg_expr.clone().field(encoder.encode_discriminant_field());
                    let variant_discriminant = size.sign_extend(discriminant_raw) as i128;

                    variants.push((
                        vir_expr! { [arg_discriminant] == [vir::Expr::from(variant_discriminant)] },
                        fields.into_iter().conjoin(),
                    ));
                }
                if variants.len() == 1 {
                    // skip discriminant call and implication if only one variant
                    conjuncts.push(variants[0].1.clone());
                } else {
                    conjuncts.extend(variants.into_iter().map(|(l, r)| vir::Expr::implies(l, r)));
                }
            }

            if let Some(specs) = encoder.get_type_specs(adt_def.did()) {
                match &specs.invariant {
                    typed::SpecificationItem::Empty => {}
                    typed::SpecificationItem::Inherent(invs) => {
                        conjuncts.extend(
                            invs.iter()
                                .map(|inherent_def_id| {
                                    encoder.encode_assertion(
                                        inherent_def_id,
                                        None, // TODO(inv): two-state invariants
                                        &[arg_expr.clone()],
                                        None,
                                        true,
                                        inherent_def_id.to_def_id(),
                                        substs,
                                    )
                                })
                                .collect::<Result<Vec<_>, _>>()?,
                        )
                    }
                    _ => todo!(),
                    // TODO(inv): handle invariant inheritance
                }
            }
        }

        // other types should not make it here because of `needs_invariant_func`
        _ => unreachable!("{ty:?}"),
    };
    let inv_body = conjuncts.into_iter().conjoin();
    let inv_func = encoder.patch_snapshots_function(encode_invariant_func_base(
        encoder,
        ty,
        Some(inv_body),
    )?)?;
    encoder.insert_function(inv_func.clone());
    Ok(inv_func)
}
