//! Helper functions for working with lifetimes.

use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use prusti_interface::environment::debug_utils::to_text::ToText;
use prusti_rustc_interface::middle::{ty, ty::SubstsRef};
use vir_crate::high as vir_high;

pub(super) fn extract_lifetimes_from_substs<'tcx>(
    type_encoder: &impl super::MirTypeEncoderInterface<'tcx>,
    substs: SubstsRef<'tcx>,
    lifetimes: &mut Vec<vir_high::ty::LifetimeConst>,
) -> SpannedEncodingResult<()> {
    for kind in substs.iter() {
        if let ty::subst::GenericArgKind::Lifetime(region) = kind.unpack() {
            lifetimes.push(vir_high::ty::LifetimeConst {
                name: region.to_text(),
            });
        }
    }
    for kind in substs.iter() {
        if let ty::subst::GenericArgKind::Type(arg_ty) = kind.unpack() {
            extract_lifetimes_from_type(type_encoder, arg_ty, lifetimes)?;
        }
    }
    Ok(())
}

pub(super) fn extract_lifetimes_from_type<'tcx>(
    type_encoder: &impl super::MirTypeEncoderInterface<'tcx>,
    ty: ty::Ty<'tcx>,
    lifetimes: &mut Vec<vir_high::ty::LifetimeConst>,
) -> SpannedEncodingResult<()> {
    match ty.kind() {
        ty::TyKind::Bool
        | ty::TyKind::Char
        | ty::TyKind::Int(_)
        | ty::TyKind::Uint(_)
        | ty::TyKind::Float(_)
        | ty::TyKind::Foreign(_)
        | ty::TyKind::Str
        | ty::TyKind::Error(_)
        | ty::TyKind::Never => {}
        ty::TyKind::Adt(_, substs)
        | ty::TyKind::Closure(_, substs)
        | ty::TyKind::Alias(ty::AliasKind::Opaque, ty::AliasTy { substs, .. })
        | ty::TyKind::FnDef(_, substs) => {
            extract_lifetimes_from_substs(type_encoder, substs, lifetimes)?
        }
        ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) => {
            extract_lifetimes_from_type(type_encoder, *ty, lifetimes)?
        }
        ty::TyKind::Dynamic(_, region, _) => lifetimes.push(vir_high::ty::LifetimeConst {
            name: region.to_text(),
        }),
        ty::TyKind::Ref(region, target_ty, _) => {
            lifetimes.push(vir_high::ty::LifetimeConst {
                name: region.to_text(),
            });
            extract_lifetimes_from_type(type_encoder, *target_ty, lifetimes)?;
        }
        ty::TyKind::Tuple(ty_list) => {
            for item_ty in ty_list.iter() {
                extract_lifetimes_from_type(type_encoder, item_ty, lifetimes)?;
            }
        }
        ty::TyKind::RawPtr(type_and_mut) => {
            extract_lifetimes_from_type(type_encoder, type_and_mut.ty, lifetimes)?
        }
        ty::TyKind::FnPtr(poly_fn_sig) => {
            let ty_list = poly_fn_sig.inputs_and_output().bound_vars();
            for bound_variable_kind in ty_list.iter() {
                if let ty::BoundVariableKind::Region(bound_region_kind) = bound_variable_kind {
                    lifetimes.push(vir_high::ty::LifetimeConst {
                        name: bound_region_kind.to_text(),
                    });
                }
            }
        }
        ty::TyKind::Param(_param_ty) => {
            // FIXME: extract lifetimes from TyKind::Param()
        }
        ty::TyKind::Alias(ty::AliasKind::Projection, alias_ty) => {
            extract_lifetimes_from_substs(type_encoder, alias_ty.substs, lifetimes)?
        }
        ty::TyKind::Bound(_, _)
        | ty::TyKind::Placeholder(_)
        | ty::TyKind::Infer(_)
        | ty::TyKind::Generator(..)
        | ty::TyKind::GeneratorWitness(_) => {
            return Err(SpannedEncodingError::unsupported(
                format!("unsupported type to extract lifetimes: {:?}", ty.kind()),
                type_encoder.get_type_definition_span(ty),
            ));
        }
    };
    Ok(())
}
