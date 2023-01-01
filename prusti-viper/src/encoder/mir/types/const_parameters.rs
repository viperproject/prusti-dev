//! Helper functions for working with const parameters.

use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use prusti_rustc_interface::middle::{ty, ty::SubstsRef};
use vir_crate::high as vir_high;

pub(super) fn extract_const_parameters_from_substs<'tcx>(
    type_encoder: &impl super::MirTypeEncoderInterface<'tcx>,
    substs: SubstsRef<'tcx>,
    const_parameters: &mut Vec<vir_high::VariableDecl>,
) -> SpannedEncodingResult<()> {
    for kind in substs.iter() {
        if let ty::subst::GenericArgKind::Type(arg_ty) = kind.unpack() {
            extract_const_parameters_from_type(type_encoder, arg_ty, const_parameters)?;
        }
    }
    Ok(())
}

pub(super) fn extract_const_parameters_from_type<'tcx>(
    type_encoder: &impl super::MirTypeEncoderInterface<'tcx>,
    ty: ty::Ty<'tcx>,
    const_parameters: &mut Vec<vir_high::VariableDecl>,
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
        | ty::TyKind::Never
        | ty::TyKind::Dynamic(..) => {}
        ty::TyKind::Adt(_, substs)
        | ty::TyKind::Closure(_, substs)
        | ty::TyKind::Alias(ty::AliasKind::Opaque, ty::AliasTy { substs, .. })
        | ty::TyKind::FnDef(_, substs) => {
            extract_const_parameters_from_substs(type_encoder, substs, const_parameters)?
        }
        ty::TyKind::Ref(_, ty, _) => {
            extract_const_parameters_from_type(type_encoder, *ty, const_parameters)?
        }
        // ty::TyKind::Slice(ty) |
        ty::TyKind::Array(ty, _) => {
            let array_len = vir_high::VariableDecl::new(
                format!("array_len${}", const_parameters.len()),
                vir_high::Type::Int(vir_high::ty::Int::Usize),
            );
            const_parameters.push(array_len);
            extract_const_parameters_from_type(type_encoder, *ty, const_parameters)?
        }
        ty::TyKind::Slice(ty) => {
            extract_const_parameters_from_type(type_encoder, *ty, const_parameters)?
        }
        ty::TyKind::Tuple(ty_list) => {
            for item_ty in ty_list.iter() {
                extract_const_parameters_from_type(type_encoder, item_ty, const_parameters)?;
            }
        }
        ty::TyKind::RawPtr(type_and_mut) => {
            extract_const_parameters_from_type(type_encoder, type_and_mut.ty, const_parameters)?
        }
        ty::TyKind::FnPtr(_) => {
            // FIXME: extract const parameters from FnPtr.
        }
        ty::TyKind::Param(_param_ty) => {
            // FIXME: extract const_parameters from TyKind::Param()
        }
        ty::TyKind::Alias(ty::AliasKind::Projection, alias_ty) => {
            extract_const_parameters_from_substs(type_encoder, alias_ty.substs, const_parameters)?
        }
        ty::TyKind::Bound(_, _)
        | ty::TyKind::Placeholder(_)
        | ty::TyKind::Infer(_)
        | ty::TyKind::Generator(..)
        | ty::TyKind::GeneratorWitness(_) => {
            return Err(SpannedEncodingError::unsupported(
                format!(
                    "unsupported type to extract const_parameters: {:?}",
                    ty.kind()
                ),
                type_encoder.get_type_definition_span(ty),
            ));
        }
    };
    Ok(())
}
