// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::PointwiseState;
use prusti_rustc_interface::{
    middle::{mir, ty, ty::TyCtxt},
    target::abi::VariantIdx,
};

use super::CouplingState;
use crate::mir_utils::Place;

impl<'mir, 'tcx: 'mir> PointwiseState<'mir, 'tcx, CouplingState<'mir, 'tcx>> {
    // TODO: Put graphviz log stuff in here.
}

// Helpers stolen from definitely accessible
fn pretty_print_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: Place<'tcx>,
) -> Option<String> {
    let mut pieces = vec![];

    // Open parenthesis
    for elem in place.projection.iter().rev() {
        match elem {
            mir::ProjectionElem::Deref => pieces.push("(*".to_string()),
            mir::ProjectionElem::Field(..) => pieces.push("(".to_string()),
            _ => {}
        }
    }

    // Skip compiler-generated variables
    if body.local_decls[place.local].from_compiler_desugaring() {
        return None;
    }

    // Find name of the local
    let local_name = body
        .var_debug_info
        .iter()
        .find(|var_debug_info| {
            if let mir::VarDebugInfoContents::Place(debug_place) = var_debug_info.value {
                if let Some(debug_local) = debug_place.as_local() {
                    return debug_local == place.local;
                }
            };
            false
        })
        .map(|var_debug_info| var_debug_info.name);
    if let Some(name) = local_name {
        pieces.push(format!("{}", name));
    } else {
        return None;
    }

    // Close parenthesis
    let mut prev_ty = body.local_decls[place.local].ty;
    let mut variant = None;
    for (proj_base, elem) in place.iter_projections() {
        match elem {
            mir::ProjectionElem::Deref => {
                pieces.push(")".to_string());
            }
            mir::ProjectionElem::Downcast(_, variant_index) => {
                prev_ty = proj_base.ty(body, tcx).ty;
                variant = Some(variant_index);
            }
            mir::ProjectionElem::Field(field, field_ty) => {
                let field_name = describe_field_from_ty(tcx, prev_ty, field, variant)?;
                pieces.push(format!(".{})", field_name));
                prev_ty = field_ty;
                variant = None;
            }
            mir::ProjectionElem::Index(..)
            | mir::ProjectionElem::ConstantIndex { .. }
            | mir::ProjectionElem::OpaqueCast(..)
            | mir::ProjectionElem::Subslice { .. } => {
                // It's not possible to move-out or borrow an individual element.
                unreachable!()
            }
        }
    }

    Some(pieces.join(""))
}

/// End-user visible description of the `field_index`nth field of `ty`
fn describe_field_from_ty(
    tcx: TyCtxt<'_>,
    ty: ty::Ty<'_>,
    field: mir::Field,
    variant_index: Option<VariantIdx>,
) -> Option<String> {
    if ty.is_box() {
        // If the type is a box, the field is described from the boxed type
        describe_field_from_ty(tcx, ty.boxed_ty(), field, variant_index)
    } else {
        match *ty.kind() {
            ty::TyKind::Adt(def, _) => {
                let variant = if let Some(idx) = variant_index {
                    assert!(def.is_enum());
                    &def.variants()[idx]
                } else {
                    def.non_enum_variant()
                };
                Some(variant.fields[field.index()].ident(tcx).to_string())
            }
            ty::TyKind::Tuple(_) => Some(field.index().to_string()),
            ty::TyKind::Ref(_, ty, _) | ty::TyKind::RawPtr(ty::TypeAndMut { ty, .. }) => {
                describe_field_from_ty(tcx, ty, field, variant_index)
            }
            ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) => {
                describe_field_from_ty(tcx, ty, field, variant_index)
            }
            ty::TyKind::Closure(..) | ty::TyKind::Generator(..) => {
                // Supporting these cases is complex
                None
            }
            _ => unreachable!("Unexpected type `{:?}`", ty),
        }
    }
}
