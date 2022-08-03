// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::utils::{self, is_prefix};
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty::TyCtxt},
};

/// A set of MIR places.
///
/// Invariant: we never have a place and any of its descendants in the
/// set at the same time. For example, having `x.f` and `x.f.g` in the
/// set at the same time is illegal.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct PlaceSet<'tcx> {
    places: FxHashSet<mir::Place<'tcx>>,
}

impl<'tcx> PlaceSet<'tcx> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn contains(&self, place: mir::Place<'tcx>) -> bool {
        self.places.contains(&place)
    }
    pub fn contains_prefix_of(&self, place: mir::Place<'tcx>) -> bool {
        self.places
            .iter()
            .any(|potential_prefix| is_prefix(place, *potential_prefix))
    }
    pub fn check_invariant(&self) {
        for place1 in self.places.iter() {
            for place2 in self.places.iter() {
                if place1 != place2 {
                    assert!(
                        !is_prefix(*place1, *place2),
                        "The place {:?} is a prefix of the place {:?}",
                        place2,
                        place1
                    );
                    assert!(
                        !is_prefix(*place2, *place1),
                        "The place {:?} is a prefix of the place {:?}",
                        place1,
                        place2
                    );
                }
            }
        }
    }
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a mir::Place<'tcx>> {
        self.places.iter()
    }
    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(self) -> impl Iterator<Item = mir::Place<'tcx>> {
        self.places.into_iter()
    }
    /// Insert `place`.
    pub fn insert(&mut self, place: mir::Place<'tcx>, mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) {
        self.check_invariant();
        // First, check that the place is not already marked as
        // definitely initialized.
        if !self.places.iter().any(|other| is_prefix(place, *other)) {
            // To maintain the invariant that we do not have a place and its
            // prefix in the set, we remove all places for which the given
            // one is a prefix.
            self.places.retain(|other| !is_prefix(*other, place));
            self.places.insert(place);
            // If all fields of a struct are definitely initialized,
            // just keep info that the struct is definitely initialized.
            utils::collapse(mir, tcx, &mut self.places, place);
        }
        self.check_invariant();
    }
    /// Remove `place`.
    pub fn remove(&mut self, place: mir::Place<'tcx>, mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) {
        self.check_invariant();
        let mut places = Vec::new();
        let old_places = std::mem::take(&mut self.places);
        // If needed, split the place whose part got uninitialized into
        // multiple places.
        for other in old_places.into_iter() {
            if is_prefix(place, other) {
                // We are uninitializing a field of the place `other`.
                places.extend(utils::expand(mir, tcx, other, place));
            } else if is_prefix(other, place) {
                // We are uninitializing a place of which only some
                // fields are initialized. Just remove all initialized
                // fields.
                // This happens when the target place is already
                // initialized.
            } else {
                places.push(other);
            }
        }
        // Check the invariant.
        for place1 in places.iter() {
            assert!(
                !is_prefix(*place1, place) && !is_prefix(place, *place1),
                "Bug: failed to ensure that there are no prefixes: place={:?} place1={:?}",
                place,
                place1
            );
            for place2 in places.iter() {
                if place1 != place2 {
                    assert!(
                        !is_prefix(*place1, *place2),
                        "The place {:?} is a prefix of the place {:?}",
                        place2,
                        place1
                    );
                    assert!(
                        !is_prefix(*place2, *place1),
                        "The place {:?} is a prefix of the place {:?}",
                        place1,
                        place2
                    );
                }
            }
        }

        self.places = places.into_iter().collect();
        self.check_invariant();
    }
    /// Compute the intersection of the two place sets.
    pub fn merge(place_set1: &PlaceSet<'tcx>, place_set2: &PlaceSet<'tcx>) -> PlaceSet<'tcx> {
        place_set1.check_invariant();
        place_set2.check_invariant();
        let mut places = FxHashSet::default();
        let mut propage_places = |place_set1: &PlaceSet<'tcx>, place_set2: &PlaceSet<'tcx>| {
            for place in place_set1.iter() {
                for potential_prefix in place_set2.iter() {
                    if is_prefix(*place, *potential_prefix) {
                        places.insert(*place);
                        break;
                    }
                }
            }
        };
        propage_places(place_set1, place_set2);
        propage_places(place_set2, place_set1);
        let result = Self { places };
        result.check_invariant();
        result
    }
    /// This function fixes the invariant.
    pub fn deduplicate(&mut self) {
        let old_places = std::mem::take(&mut self.places);
        let places: Vec<_> = old_places.into_iter().collect();
        let mut to_remove = FxHashSet::default();
        for (i, place) in places.iter().enumerate() {
            for (j, other) in places.iter().enumerate() {
                if i <= j {
                    continue;
                }
                if place == other {
                    to_remove.insert(j);
                } else if is_prefix(*place, *other) {
                    to_remove.insert(i);
                } else if is_prefix(*other, *place) {
                    to_remove.insert(j);
                }
            }
        }
        for (i, place) in places.into_iter().enumerate() {
            if !to_remove.contains(&i) {
                self.places.insert(place);
            }
        }
        self.check_invariant();
    }
    /// Compute the union of the two place sets.
    ///
    /// Note that this function may break the invariant that we never
    /// have a place and its descendants in the set.
    pub fn union(place_set1: &PlaceSet<'tcx>, place_set2: &PlaceSet<'tcx>) -> PlaceSet<'tcx> {
        let mut places = place_set1.places.clone();
        places.extend(place_set2.iter().cloned());
        Self { places }
    }
}

impl<'tcx> From<FxHashSet<mir::Place<'tcx>>> for PlaceSet<'tcx> {
    fn from(places: FxHashSet<mir::Place<'tcx>>) -> Self {
        Self { places }
    }
}
