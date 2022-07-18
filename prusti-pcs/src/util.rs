// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use analysis::mir_utils::expand_struct_place;
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    errors::MultiSpan,
    middle::{
        mir::{self, Body, LocalDecl, Place},
        ty::{self, TyCtxt},
    },
};

/// Wrapper type for all errors
pub type EncodingResult<A> = Result<A, PrustiError>;

#[allow(dead_code)]
/// retrieve local_decl from a place in a MIR context
fn retrieve_local_decl<'a, 'tcx: 'a>(
    mir: &'a Body<'tcx>,
    p: &'a Place<'tcx>,
) -> EncodingResult<&'a LocalDecl<'tcx>> {
    match mir.local_decls.get(p.local) {
        Some(decl) => Ok(decl),
        None => Err(PrustiError::internal(
            format!("error when retrieving local_decl for place {:#?}", p),
            MultiSpan::new(),
        )),
    }
}

/// Retruns a collection of immediate subplaces
/// (Modified from analysis/mir_utils)
pub fn expand_place<'mir, 'tcx: 'mir>(
    place: Place<'tcx>,
    mir: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> EncodingResult<Vec<Place<'tcx>>> {
    match place.projection[place.projection.len()] {
        mir::ProjectionElem::Field(projected_field, field_ty) => {
            let mut places = expand_struct_place(place, mir, tcx, Some(projected_field.index()));
            let new_current_place = tcx.mk_place_field(place, projected_field, field_ty).into();
            // TODO: Is this correct?
            places.push(new_current_place);
            Ok(places)
        }
        mir::ProjectionElem::Downcast(_symbol, variant) => {
            let kind = &place.ty(mir, tcx).ty.kind();
            if let ty::TyKind::Adt(adt, _) = kind {
                Ok(vec![tcx.mk_place_downcast(place, *adt, variant).into()])
            } else {
                Err(PrustiError::internal(
                    format!("unreachable state in expansion of downcast"),
                    MultiSpan::new(),
                ))
            }
        }
        mir::ProjectionElem::Deref => Ok(vec![tcx.mk_place_deref(place).into()]),
        mir::ProjectionElem::Index(idx) => Ok(vec![tcx.mk_place_index(place, idx).into()]),
        elem => Err(PrustiError::unsupported(
            format!("expansion of place {:#?} unsuppoted", elem),
            MultiSpan::new(),
        )),
    }
}
