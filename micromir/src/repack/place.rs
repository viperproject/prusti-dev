// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{
        mir::{Body, Field, ProjectionElem},
        ty::{TyCtxt, TyKind},
    },
};

use crate::Place;

#[derive(Copy, Clone)]
// TODO: modified version of fns taken from `prusti-interface/src/utils.rs`; deduplicate
pub(crate) struct PlaceRepacker<'a, 'tcx: 'a> {
    mir: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx: 'a> PlaceRepacker<'a, 'tcx> {
    pub fn new(mir: &'a Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self { mir, tcx }
    }

    /// Expand `current_place` one level down by following the `guide_place`.
    /// Returns the new `current_place` and a vector containing other places that
    /// could have resulted from the expansion.
    #[tracing::instrument(level = "trace", skip(self), ret)]
    pub(crate) fn expand_one_level(
        self,
        current_place: Place<'tcx>,
        guide_place: Place<'tcx>,
    ) -> (Place<'tcx>, Vec<Place<'tcx>>) {
        let index = current_place.projection.len();
        let new_projection = self.tcx.mk_place_elems(
            current_place
                .projection
                .iter()
                .chain([guide_place.projection[index]]),
        );
        let new_current_place = Place::new(current_place.local, new_projection);
        let other_places = match guide_place.projection[index] {
            ProjectionElem::Field(projected_field, _field_ty) => {
                self.expand_place(current_place, Some(projected_field.index()))
            }
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => (0..min_length)
                .into_iter()
                .filter(|&i| {
                    if from_end {
                        i != min_length - offset
                    } else {
                        i != offset
                    }
                })
                .map(|i| {
                    self.tcx
                        .mk_place_elem(
                            *current_place,
                            ProjectionElem::ConstantIndex {
                                offset: i,
                                min_length,
                                from_end,
                            },
                        )
                        .into()
                })
                .collect(),
            ProjectionElem::Deref
            | ProjectionElem::Index(..)
            | ProjectionElem::Subslice { .. }
            | ProjectionElem::Downcast(..)
            | ProjectionElem::OpaqueCast(..) => vec![],
        };
        (new_current_place, other_places)
    }

    /// Expands a place `x.f.g` of type struct into a vector of places for
    /// each of the struct's fields `{x.f.g.f, x.f.g.g, x.f.g.h}`. If
    /// `without_field` is not `None`, then omits that field from the final
    /// vector.
    pub fn expand_place(
        self,
        place: Place<'tcx>,
        without_field: Option<usize>,
    ) -> Vec<Place<'tcx>> {
        let mut places = Vec::new();
        let typ = place.ty(self.mir, self.tcx);
        if !matches!(typ.ty.kind(), TyKind::Adt(..)) {
            assert!(
                typ.variant_index.is_none(),
                "We have assumed that only enums can have variant_index set. Got {typ:?}."
            );
        }
        match typ.ty.kind() {
            TyKind::Adt(def, substs) => {
                let variant = typ
                    .variant_index
                    .map(|i| def.variant(i))
                    .unwrap_or_else(|| def.non_enum_variant());
                for (index, field_def) in variant.fields.iter().enumerate() {
                    if Some(index) != without_field {
                        let field = Field::from_usize(index);
                        let field_place =
                            self.tcx
                                .mk_place_field(*place, field, field_def.ty(self.tcx, substs));
                        places.push(field_place.into());
                    }
                }
            }
            TyKind::Tuple(slice) => {
                for (index, arg) in slice.iter().enumerate() {
                    if Some(index) != without_field {
                        let field = Field::from_usize(index);
                        let field_place = self.tcx.mk_place_field(*place, field, arg);
                        places.push(field_place.into());
                    }
                }
            }
            TyKind::Closure(_, substs) => {
                for (index, subst_ty) in substs.as_closure().upvar_tys().enumerate() {
                    if Some(index) != without_field {
                        let field = Field::from_usize(index);
                        let field_place = self.tcx.mk_place_field(*place, field, subst_ty);
                        places.push(field_place.into());
                    }
                }
            }
            TyKind::Generator(_, substs, _) => {
                for (index, subst_ty) in substs.as_generator().upvar_tys().enumerate() {
                    if Some(index) != without_field {
                        let field = Field::from_usize(index);
                        let field_place = self.tcx.mk_place_field(*place, field, subst_ty);
                        places.push(field_place.into());
                    }
                }
            }
            ty => unreachable!("ty={:?}", ty),
        }
        places
    }

    /// Subtract the `subtrahend` place from the `minuend` place. The
    /// subtraction is defined as set minus between `minuend` place replaced
    /// with a set of places that are unrolled up to the same level as
    /// `subtrahend` and the singleton `subtrahend` set. For example,
    /// `expand(x.f, x.f.g.h)` is performed by unrolling `x.f` into
    /// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
    /// subtracting `{x.f.g.h}` from it, which results into (`{x.f, x.f.g}`, `{x.g, x.h,
    /// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`). The first vector contains the chain of
    /// places that were expanded along with the target subtrahend of each expansion.
    #[tracing::instrument(level = "trace", skip(self), ret)]
    pub fn expand(
        self,
        mut minuend: Place<'tcx>,
        subtrahend: Place<'tcx>,
    ) -> (Vec<(Place<'tcx>, Place<'tcx>)>, Vec<Place<'tcx>>) {
        assert!(
            minuend.is_prefix(subtrahend),
            "The minuend ({minuend:?}) must be the prefix of the subtrahend ({subtrahend:?})."
        );
        let mut place_set = Vec::new();
        let mut expanded = Vec::new();
        while minuend.projection.len() < subtrahend.projection.len() {
            expanded.push((minuend, subtrahend));
            let (new_minuend, places) = self.expand_one_level(minuend, subtrahend);
            minuend = new_minuend;
            place_set.extend(places);
        }
        (expanded, place_set)
    }

    /// Try to collapse all places in `places` by following the
    /// `guide_place`. This function is basically the reverse of
    /// `expand`.
    #[tracing::instrument(level = "trace", skip(self), ret)]
    pub fn collapse(
        self,
        guide_place: Place<'tcx>,
        places: &mut FxHashSet<Place<'tcx>>,
    ) -> Vec<(Place<'tcx>, Place<'tcx>)> {
        let mut collapsed = Vec::new();
        let mut guide_places = vec![guide_place];
        while let Some(guide_place) = guide_places.pop() {
            if !places.remove(&guide_place) {
                let expand_guide = *places
                    .iter()
                    .find(|p| guide_place.is_prefix(**p))
                    .unwrap_or_else(|| {
                        panic!(
                            "The `places` set didn't contain all \
                            the places required to construct the \
                            `guide_place`. Currently tried to find \
                            `{guide_place:?}` in `{places:?}`."
                        )
                    });
                let (expanded, new_places) = self.expand(guide_place, expand_guide);
                // Doing `collapsed.extend(expanded)` would result in a reversed order.
                // Could also change this to `collapsed.push(expanded)` and return Vec<Vec<_>>.
                collapsed.extend(expanded);
                guide_places.extend(new_places);
                places.remove(&expand_guide);
            }
        }
        collapsed.reverse();
        collapsed
    }

    // /// Pop the last projection from the place and return the new place with the popped element.
    // pub fn pop_one_level(self, place: Place<'tcx>) -> (PlaceElem<'tcx>, Place<'tcx>) {
    //     assert!(place.projection.len() > 0);
    //     let last_index = place.projection.len() - 1;
    //     let projection = self.tcx.intern_place_elems(&place.projection[..last_index]);
    //     (
    //         place.projection[last_index],
    //         Place::new(place.local, projection),
    //     )
    // }

    #[tracing::instrument(level = "debug", skip(self), ret, fields(lp = ?left.projection, rp = ?right.projection))]
    pub fn common_prefix(self, left: Place<'tcx>, right: Place<'tcx>) -> Place<'tcx> {
        assert_eq!(left.local, right.local);

        let common_prefix = left
            .compare_projections(right)
            .take_while(|(eq, _, _)| *eq)
            .map(|(_, e1, _)| e1);
        Place::new(left.local, self.tcx.mk_place_elems(common_prefix))
    }

    #[tracing::instrument(level = "info", skip(self), ret)]
    pub fn joinable_to(self, from: Place<'tcx>, to: Place<'tcx>) -> Place<'tcx> {
        assert!(from.is_prefix(to));
        let proj = from.projection.iter();
        let to_proj = to.projection[from.projection.len()..]
            .iter()
            .copied()
            .take_while(|p| {
                matches!(
                    p,
                    ProjectionElem::Deref
                        | ProjectionElem::Field(..)
                        | ProjectionElem::ConstantIndex { .. }
                )
            });
        let projection = self.tcx.mk_place_elems(proj.chain(to_proj));
        Place::new(from.local, projection)
    }
}
