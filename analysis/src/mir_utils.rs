// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various helper functions for working with `mir` types.
//! copied from prusti-interface/utils

use prusti_rustc_interface::{
    abi::FieldIdx,
    data_structures::fx::FxHashSet,
    infer::infer::TyCtxtInferExt,
    middle::{
        mir,
        ty::{self, TyCtxt},
    },
    trait_selection::infer::InferCtxtExt,
};
use std::mem;

#[repr(transparent)]
#[derive(Clone, Copy, Eq, PartialEq, derive_more::From, Hash)]
/// A wrapper for `mir::Place` that implements `Ord`.
pub struct Place<'tcx>(mir::Place<'tcx>);

/// A trait enabling `Place` and `mir::Place` to be treated in the same way
pub trait PlaceImpl<'tcx> {
    fn from_mir_place(_: mir::Place<'tcx>) -> Self;
    fn to_mir_place(self) -> mir::Place<'tcx>;
}

impl<'tcx> From<mir::Local> for Place<'tcx> {
    fn from(local: mir::Local) -> Self {
        Self(local.into())
    }
}

impl<'tcx> PartialOrd for Place<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'tcx> Ord for Place<'tcx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0
            .local
            .cmp(&other.0.local)
            .then(self.0.projection.cmp(other.0.projection))
    }
}

impl<'tcx> std::fmt::Debug for Place<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<'tcx> std::ops::Deref for Place<'tcx> {
    type Target = mir::Place<'tcx>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'tcx> PlaceImpl<'tcx> for Place<'tcx> {
    fn from_mir_place(place: mir::Place<'tcx>) -> Place<'tcx> {
        Place(place)
    }
    fn to_mir_place(self) -> mir::Place<'tcx> {
        self.0
    }
}

impl<'tcx> PlaceImpl<'tcx> for mir::Place<'tcx> {
    fn from_mir_place(place: mir::Place<'tcx>) -> mir::Place<'tcx> {
        place
    }
    fn to_mir_place(self) -> mir::Place<'tcx> {
        self
    }
}

/// Convert a `location` to a string representing the statement or terminator at that `location`
pub fn location_to_stmt_str(location: mir::Location, mir: &mir::Body) -> String {
    let bb_mir = &mir[location.block];
    if location.statement_index < bb_mir.statements.len() {
        let stmt = &bb_mir.statements[location.statement_index];
        format!("{stmt:?}")
    } else {
        // location = terminator
        let terminator = bb_mir.terminator();
        format!("{:?}", terminator.kind)
    }
}

/// Check if the place `potential_prefix` is a prefix of `place`. For example:
///
/// +   `is_prefix(x.f, x.f) == true`
/// +   `is_prefix(x.f.g, x.f) == true`
/// +   `is_prefix(x.f, x.f.g) == false`
pub(crate) fn is_prefix<'tcx>(place: Place<'tcx>, potential_prefix: Place<'tcx>) -> bool {
    if place.local != potential_prefix.local
        || place.projection.len() < potential_prefix.projection.len()
    {
        false
    } else {
        place
            .projection
            .iter()
            .zip(potential_prefix.projection.iter())
            .all(|(e1, e2)| e1 == e2)
    }
}

/// Expands a place `x.f.g` of type struct into a vector of places for
/// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
/// `without_field` is not `None`, then omits that field from the final
/// vector.
pub fn expand_struct_place<'tcx, P: PlaceImpl<'tcx> + std::marker::Copy>(
    place: P,
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    without_field: Option<usize>,
) -> Vec<P> {
    let mut places: Vec<P> = Vec::new();
    let typ = place.to_mir_place().ty(mir, tcx);
    if !matches!(typ.ty.kind(), ty::Adt(..)) {
        assert!(
            typ.variant_index.is_none(),
            "We have assumed that only enums can have variant_index set. Got {typ:?}."
        );
    }
    match typ.ty.kind() {
        ty::Adt(def, substs) => {
            let variant = typ
                .variant_index
                .map(|i| def.variant(i))
                .unwrap_or_else(|| def.non_enum_variant());
            for (index, field_def) in variant.fields.iter().enumerate() {
                if Some(index) != without_field {
                    let field = FieldIdx::from_usize(index);
                    let field_place =
                        tcx.mk_place_field(place.to_mir_place(), field, field_def.ty(tcx, substs));
                    places.push(P::from_mir_place(field_place));
                }
            }
        }
        ty::Tuple(slice) => {
            for (index, arg) in slice.iter().enumerate() {
                if Some(index) != without_field {
                    let field = FieldIdx::from_usize(index);
                    let field_place = tcx.mk_place_field(place.to_mir_place(), field, arg);
                    places.push(P::from_mir_place(field_place));
                }
            }
        }
        ty::Closure(_, substs) => {
            for (index, subst_ty) in substs.as_closure().upvar_tys().iter().enumerate() {
                if Some(index) != without_field {
                    let field = FieldIdx::from_usize(index);
                    let field_place = tcx.mk_place_field(place.to_mir_place(), field, subst_ty);
                    places.push(P::from_mir_place(field_place));
                }
            }
        }
        ty::Generator(_, substs, _) => {
            for (index, subst_ty) in substs.as_generator().upvar_tys().iter().enumerate() {
                if Some(index) != without_field {
                    let field = FieldIdx::from_usize(index);
                    let field_place = tcx.mk_place_field(place.to_mir_place(), field, subst_ty);
                    places.push(P::from_mir_place(field_place));
                }
            }
        }
        ty => unreachable!("ty={:?}", ty),
    }
    places
}

/// Expand `current_place` one level down by following the `guide_place`.
/// Returns the new `current_place` and a vector containing other places that
/// could have resulted from the expansion.
pub fn expand_one_level<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    current_place: Place<'tcx>,
    guide_place: Place<'tcx>,
) -> (Place<'tcx>, Vec<Place<'tcx>>) {
    let index = current_place.projection.len();
    let new_projection = tcx.mk_place_elems_from_iter(
        current_place
            .projection
            .iter()
            .chain([guide_place.projection[index]]),
    );
    let new_current_place = Place(mir::Place {
        local: current_place.local,
        projection: new_projection,
    });
    let other_places = match guide_place.projection[index] {
        mir::ProjectionElem::Field(projected_field, _field_ty) => {
            expand_struct_place(current_place, mir, tcx, Some(projected_field.index()))
        }
        mir::ProjectionElem::Deref
        | mir::ProjectionElem::Index(..)
        | mir::ProjectionElem::ConstantIndex { .. }
        | mir::ProjectionElem::Subslice { .. }
        | mir::ProjectionElem::Downcast(..)
        | mir::ProjectionElem::OpaqueCast(..) => vec![],
    };
    (new_current_place, other_places)
}

/// Subtract the `subtrahend` place from the `minuend` place. The
/// subtraction is defined as set minus between `minuend` place replaced
/// with a set of places that are unrolled up to the same level as
/// `subtrahend` and the singleton `subtrahend` set. For example,
/// `subtract(x.f, x.f.g.h)` is performed by unrolling `x.f` into
/// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
/// subtracting `{x.f.g.h}` from it, which results into `{x.g, x.h,
/// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`.
#[tracing::instrument(level = "trace", skip(mir, tcx), ret)]
pub(crate) fn expand<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    mut minuend: Place<'tcx>,
    subtrahend: Place<'tcx>,
) -> Vec<Place<'tcx>> {
    assert!(
        is_prefix(subtrahend, minuend),
        "The minuend must be the prefix of the subtrahend."
    );
    let mut place_set = Vec::new();
    while minuend.projection.len() < subtrahend.projection.len() {
        let (new_minuend, places) = expand_one_level(mir, tcx, minuend, subtrahend);
        minuend = new_minuend;
        place_set.extend(places);
    }
    place_set
}

/// Try to collapse all places in `places` by following the
/// `guide_place`. This function is basically the reverse of
/// `expand_struct_place`.
pub(crate) fn collapse<'tcx>(
    mir: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    places: &mut FxHashSet<Place<'tcx>>,
    guide_place: Place<'tcx>,
) {
    fn recurse<'tcx>(
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        places: &mut FxHashSet<Place<'tcx>>,
        current_place: Place<'tcx>,
        guide_place: Place<'tcx>,
    ) {
        if current_place != guide_place {
            let (new_current_place, mut expansion) =
                expand_one_level(mir, tcx, current_place, guide_place);
            recurse(mir, tcx, places, new_current_place, guide_place);
            expansion.push(new_current_place);
            if expansion.iter().all(|place| places.contains(place)) {
                for place in expansion {
                    places.remove(&place);
                }
                places.insert(current_place);
            }
        }
    }
    recurse(mir, tcx, places, guide_place.local.into(), guide_place);
}

/// Remove all extensions of a place from a set, unpacking prefixes as much as needed.
pub fn remove_place_from_set<'tcx>(
    body: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    to_remove: Place<'tcx>,
    set: &mut FxHashSet<Place<'tcx>>,
) {
    let old_set = mem::take(set);
    for old_place in old_set {
        if is_prefix(to_remove, old_place) {
            // Unpack `old_place` and remove `to_remove`.
            set.extend(expand(body, tcx, old_place, to_remove));
        } else if is_prefix(old_place, to_remove) {
            // `to_remove` is a prefix of `old_place`. So, it should *not* be added to `set`.
        } else {
            // `old_place` and `to_remove` are unrelated.
            set.insert(old_place);
        }
    }
}

pub fn is_copy<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
) -> bool {
    if let ty::TyKind::Ref(_, _, mutability) = ty.kind() {
        // Shared references are copy, mutable references are not.
        // `type_implements_trait` doesn't consider that.
        matches!(mutability, mir::Mutability::Not)
    } else if let Some(copy_trait) = tcx.lang_items().copy_trait() {
        let infcx = tcx.infer_ctxt().build();
        // If `ty` has any inference variables (e.g. a region variable), then using it with
        // the freshly-created `InferCtxt` (i.e. `tcx.infer_ctxt().enter(..)`) will cause
        // a panic, since those inference variables don't exist in the new `InferCtxt`.
        // See: https://rust-lang.zulipchat.com/#narrow/stream/182449-t-compiler.2Fhelp/topic/.E2.9C.94.20Panic.20in.20is_copy_modulo_regions
        infcx
            .type_implements_trait(copy_trait, [infcx.freshen(ty)], param_env)
            .must_apply_considering_regions()
    } else {
        false
    }
}

/// Given an assignment `let _ = & <borrowed_place>`, this function returns the place that is
/// blocked by the loan.
/// For example, `let _ = &x.f.g` blocks just `x.f.g`, but `let _ = &x.f[0].g` blocks `x.f`.
pub fn get_blocked_place<'tcx>(tcx: TyCtxt<'tcx>, borrowed: Place<'tcx>) -> Place<'tcx> {
    for (place_ref, place_elem) in borrowed.iter_projections() {
        match place_elem {
            mir::ProjectionElem::Deref
            | mir::ProjectionElem::Index(..)
            | mir::ProjectionElem::ConstantIndex { .. }
            | mir::ProjectionElem::Subslice { .. } => {
                return (mir::Place {
                    local: place_ref.local,
                    projection: tcx.mk_place_elems(place_ref.projection),
                })
                .into();
            }
            mir::ProjectionElem::Field(..)
            | mir::ProjectionElem::Downcast(..)
            | mir::ProjectionElem::OpaqueCast(..) => {
                // Continue
            }
        }
    }
    borrowed
}
