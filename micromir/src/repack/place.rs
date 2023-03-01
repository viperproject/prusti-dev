// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cmp::Ordering;

use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{
        mir::{Body, Place, PlaceElem, ProjectionElem},
        ty::TyCtxt,
    },
};

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

    /// Check if the place `left` is a prefix of `right` or vice versa. For example:
    ///
    /// +   `partial_cmp(x.f, y.f) == None`
    /// +   `partial_cmp(x.f, x.g) == None`
    /// +   `partial_cmp(x.f, x.f) == Some(Ordering::Equal)`
    /// +   `partial_cmp(x.f.g, x.f) == Some(Ordering::Greater)`
    /// +   `partial_cmp(x.f, x.f.g) == Some(Ordering::Less)`
    pub fn partial_cmp(left: Place<'tcx>, right: Place<'tcx>) -> Option<Ordering> {
        if left.local != right.local {
            return None;
        }
        if left
            .projection
            .iter()
            .zip(right.projection.iter())
            .any(|(e1, e2)| e1 != e2)
        {
            return None;
        }
        Some(left.projection.len().cmp(&right.projection.len()))
    }

    /// Check if the place `potential_prefix` is a prefix of `place`. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == true`
    /// +   `is_prefix(x.f, x.f.g) == true`
    /// +   `is_prefix(x.f.g, x.f) == false`
    fn is_prefix(potential_prefix: Place<'tcx>, place: Place<'tcx>) -> bool {
        Self::partial_cmp(potential_prefix, place)
            .map(|o| o != Ordering::Greater)
            .unwrap_or(false)
    }

    /// Expand `current_place` one level down by following the `guide_place`.
    /// Returns the new `current_place` and a vector containing other places that
    /// could have resulted from the expansion.
    fn expand_one_level(
        self,
        current_place: Place<'tcx>,
        guide_place: Place<'tcx>,
    ) -> (Place<'tcx>, Vec<Place<'tcx>>) {
        use analysis::mir_utils::{expand_one_level, PlaceImpl};
        let res = expand_one_level(self.mir, self.tcx, current_place.into(), guide_place.into());
        (
            res.0.to_mir_place(),
            res.1.into_iter().map(PlaceImpl::to_mir_place).collect(),
        )
    }

    /// Subtract the `subtrahend` place from the `minuend` place. The
    /// subtraction is defined as set minus between `minuend` place replaced
    /// with a set of places that are unrolled up to the same level as
    /// `subtrahend` and the singleton `subtrahend` set. For example,
    /// `subtract(x.f, x.f.g.h)` is performed by unrolling `x.f` into
    /// `{x.g, x.h, x.f.f, x.f.h, x.f.g.f, x.f.g.g, x.f.g.h}` and
    /// subtracting `{x.f.g.h}` from it, which results into (`{x.f, x.f.g}`, `{x.g, x.h,
    /// x.f.f, x.f.h, x.f.g.f, x.f.g.g}`).
    #[tracing::instrument(level = "debug", skip(self), ret)]
    pub fn expand(
        self,
        mut minuend: Place<'tcx>,
        subtrahend: Place<'tcx>,
    ) -> (Vec<Place<'tcx>>, Vec<Place<'tcx>>) {
        assert!(
            Self::is_prefix(minuend, subtrahend),
            "The minuend ({minuend:?}) must be the prefix of the subtrahend ({subtrahend:?})."
        );
        let mut place_set = Vec::new();
        let mut expanded = Vec::new();
        while minuend.projection.len() < subtrahend.projection.len() {
            expanded.push(minuend);
            let (new_minuend, places) = self.expand_one_level(minuend, subtrahend);
            minuend = new_minuend;
            place_set.extend(places);
        }
        (expanded, place_set)
    }

    /// Try to collapse all places in `places` by following the
    /// `guide_place`. This function is basically the reverse of
    /// `expand`.
    pub fn collapse(
        self,
        guide_place: Place<'tcx>,
        places: &mut FxHashSet<Place<'tcx>>,
    ) -> Vec<Place<'tcx>> {
        let mut collapsed = Vec::new();
        let mut guide_places = vec![guide_place];
        while let Some(guide_place) = guide_places.pop() {
            if !places.remove(&guide_place) {
                let expand_guide = *places
                    .iter()
                    .find(|p| Self::is_prefix(guide_place, **p))
                    .unwrap_or_else(|| {
                        panic!(
                            "The `places` set didn't contain all \
                            the places required to construct the \
                            `guide_place`. Currently tried to find \
                            `{guide_place:?}` in `{places:?}`."
                        )
                    });
                let (mut expanded, new_places) = self.expand(guide_place, expand_guide);
                // Doing `collapsed.extend(expanded)` would result in a reversed order.
                // Could also change this to `collapsed.push(expanded)` and return Vec<Vec<_>>.
                expanded.extend(collapsed);
                collapsed = expanded;
                guide_places.extend(new_places);
                places.remove(&expand_guide);
            }
        }
        collapsed
    }

    /// Pop the last projection from the place and return the new place with the popped element.
    pub fn try_pop_one_level(self, place: Place<'tcx>) -> Option<(PlaceElem<'tcx>, Place<'tcx>)> {
        if place.projection.len() > 0 {
            let last_index = place.projection.len() - 1;
            let new_place = Place {
                local: place.local,
                projection: self.tcx.intern_place_elems(&place.projection[..last_index]),
            };
            Some((place.projection[last_index], new_place))
        } else {
            None
        }
    }

    // /// Pop the last element from the place if it is a dereference.
    // pub fn try_pop_deref(self, place: Place<'tcx>) -> Option<Place<'tcx>> {
    //     self.try_pop_one_level(place).and_then(|(elem, base)| {
    //         if let ProjectionElem::Deref = elem {
    //             Some(base)
    //         } else {
    //             None
    //         }
    //     })
    // }

    pub fn pop_till_enum(self, place: Place<'tcx>) -> Place<'tcx> {
        let (mut elem, mut base) = self.try_pop_one_level(place).unwrap();
        while !matches!(elem, ProjectionElem::Downcast(..)) {
            let (new_elem, new_base) = self.try_pop_one_level(base).unwrap();
            elem = new_elem;
            base = new_base;
        }
        base
    }

    /// Checks if we can expand either place to the other, without going through an enum.
    /// If we can reach from one to the other, but need to go through an enum, we return `Err`.
    pub fn expandable_no_enum(
        left: Place<'tcx>,
        right: Place<'tcx>,
    ) -> Option<Result<Ordering, Ordering>> {
        let ord = Self::partial_cmp(left, right)?;
        let (minuend, subtrahend) = match ord {
            Ordering::Greater => (right, left),
            Ordering::Less => (left, right),
            Ordering::Equal => return Some(Ok(Ordering::Equal)),
        };
        if subtrahend
            .projection
            .iter()
            .skip(minuend.projection.len())
            .any(|elem| matches!(elem, ProjectionElem::Downcast(..)))
        {
            Some(Err(ord))
        } else {
            Some(Ok(ord))
        }
    }
}
