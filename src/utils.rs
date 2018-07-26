// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various helper functions for working with `mir::Place`.

use rustc_data_structures::indexed_vec::Idx;
use rustc::mir;
use rustc::ty::{self, TyCtxt};
use std::collections::HashSet;

/// Check if the place `potential_prefix` is a prefix of `place`. For example:
///
/// +   `is_prefix(x.f, x.f) == true`
/// +   `is_prefix(x.f.g, x.f) == true`
/// +   `is_prefix(x.f, x.f.g) == false`
pub fn is_prefix(place: &mir::Place, potential_prefix: &mir::Place) -> bool {
    if place == potential_prefix {
        true
    } else {
        match place {
            mir::Place::Local(_) => false,
            mir::Place::Projection(box mir::Projection { base, .. }) => {
                is_prefix(base, potential_prefix)
            }
            _ => unimplemented!(),
        }
    }
}

/// Expands a place `x.f.g` of type struct into a vector of places for
/// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
/// `without_field` is not `None`, then omits that field from the final
/// vector.
pub fn expand_struct_place<'a, 'tcx: 'a>(
    place: &mir::Place<'tcx>,
    mir: &mir::Mir<'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    without_field: Option<mir::Field>,
) -> Vec<mir::Place<'tcx>> {
    let mut places = Vec::new();
    match place.ty(mir, tcx) {
        mir::tcx::PlaceTy::Ty { ty: base_ty } => match base_ty.sty {
            ty::TyAdt(def, substs) => {
                assert!(
                    def.variants.len() == 1,
                    "Only structs can be expanded. Got def={:?}.",
                    def
                );
                for (index, field_def) in def.variants[0].fields.iter().enumerate() {
                    let field = mir::Field::new(index);
                    if Some(field) != without_field {
                        places.push(place.clone().field(field, field_def.ty(tcx, substs)));
                    }
                }
            }
            ref ty => {
                unimplemented!("ty={:?}", ty);
            }
        },
        mir::tcx::PlaceTy::Downcast { .. } => {}
        base_ty => {
            unimplemented!("base_ty={:?}", base_ty);
        }
    }
    places
}

/// Subtract the `subtrahend` place from the `minuend` place. The
/// subtraction is defined as set minus between `minuend` place replaced
/// with a set of places that are unrolled up to the same level as
/// `subtrahend` and the singleton `subtrahend` set. For example,
/// `subtract(x.f, x.f.g.h)` is performed by unrolling `x.f` into
/// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
/// subtracting `{x.f.g.h}` from it, which results into `{x.g, x.h,
/// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`.
pub fn expand<'a, 'tcx: 'a>(
    mir: &mir::Mir<'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    minuend: &mir::Place<'tcx>,
    subtrahend: &mir::Place<'tcx>,
) -> Vec<mir::Place<'tcx>> {
    assert!(
        is_prefix(subtrahend, minuend),
        "The minuend must be the prefix of the subtrahend."
    );
    let mut place_set = Vec::new();
    fn expand_recursively<'a, 'tcx: 'a>(
        place_set: &mut Vec<mir::Place<'tcx>>,
        mir: &mir::Mir<'tcx>,
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        minuend: &mir::Place<'tcx>,
        subtrahend: &mir::Place<'tcx>,
    ) {
        if minuend != subtrahend {
            match subtrahend {
                mir::Place::Projection(box mir::Projection { base, elem }) => {
                    // We just recurse until both paths become equal.
                    expand_recursively(place_set, mir, tcx, minuend, base);
                    match elem {
                        mir::ProjectionElem::Field(projected_field, _field_ty) => {
                            let places =
                                expand_struct_place(base, mir, tcx, Some(*projected_field));
                            place_set.extend(places);
                        }
                        mir::ProjectionElem::Downcast(def, variant) => {}
                        elem => {
                            unimplemented!("elem = {:?}", elem);
                        }
                    }
                }
                _ => unreachable!(),
            }
        }
    };
    expand_recursively(&mut place_set, mir, tcx, minuend, subtrahend);
    trace!(
        "expand minuend={:?} subtrahend={:?} place_set={:?}",
        minuend,
        subtrahend,
        place_set
    );
    place_set
}

/// Try to collapse all places in `places` by following the
/// `guide_place`. This function is basically the reverse of
/// `expand_struct_place`.
pub fn collapse<'a, 'tcx: 'a>(
    mir: &mir::Mir<'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    places: &mut HashSet<mir::Place<'tcx>>,
    guide_place: &mir::Place<'tcx>,
) {
    let mut guide_place = guide_place.clone();
    while let mir::Place::Projection(box mir::Projection { base, elem }) = guide_place {
        let expansion = expand_struct_place(&base, mir, tcx, None);
        if expansion.iter().all(|place| places.contains(place)) {
            for place in expansion {
                places.remove(&place);
            }
            places.insert(base.clone());
        } else {
            return;
        }
        guide_place = base;
    }
}
