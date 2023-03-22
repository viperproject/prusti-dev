// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    data_structures::{fx::FxHashSet, graph::WithStartNode},
    dataflow::{storage, Analysis, ResultsCursor, AnalysisDomain, JoinSemiLattice, CallReturnPlaces,
        impls::{MaybeStorageLive, MaybeBorrowedLocals, MaybeRequiresStorage, MaybeLiveLocals}},
    index::vec::{Idx, IndexVec},
    middle::{
        mir::{Statement, Location, Terminator, Body, BasicBlock, HasLocalDecls, Local, RETURN_PLACE},
        ty::TyCtxt,
    },
};

use crate::{
    CapabilityKind, CapabilityLocal, utils::PlaceRepacker, RepackOp, CapabilityProjections, Fpcs, CapabilitySummary, PlaceOrdering
};

impl JoinSemiLattice for Fpcs<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        self.summary.join(&other.summary, self.repacker)
    }
}

trait RepackingJoinSemiLattice<'tcx> {
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> bool;
}
impl<'tcx> RepackingJoinSemiLattice<'tcx> for CapabilitySummary<'tcx> {
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        let mut changed = false;
        for (l, to) in self.iter_enumerated_mut() {
            let local_changed = to.join(&other[l], repacker);
            changed = changed || local_changed;
        }
        changed
    }
}

impl<'tcx> RepackingJoinSemiLattice<'tcx> for CapabilityLocal<'tcx> {
    // #[tracing::instrument(level = "debug", skip(repacker))]
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        match (&mut *self, other) {
            (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => false,
            (CapabilityLocal::Allocated(to_places), CapabilityLocal::Allocated(from_places)) => {
                to_places.join(from_places, repacker)
            }
            (CapabilityLocal::Allocated(..), CapabilityLocal::Unallocated) => {
                *self = CapabilityLocal::Unallocated;
                true
            }
            // Can jump to a `is_cleanup` block with some paths being alloc and other not
            (CapabilityLocal::Unallocated, CapabilityLocal::Allocated(..)) => false,
        }
    }
}


impl<'tcx> RepackingJoinSemiLattice<'tcx> for CapabilityProjections<'tcx> {
    // #[tracing::instrument(name = "CapabilityProjections::join", level = "trace", skip(repacker))]
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        let mut changed = false;
        for (&place, &kind) in &**other {
            let related = self.find_all_related(place, None);
            match related.relation {
                PlaceOrdering::Prefix => {
                    changed = true;

                    let from = related.from[0].0;
                    let joinable_place = repacker.joinable_to(from, place);
                    if joinable_place != from {
                        self.unpack(from, joinable_place, repacker);
                    }
                    // Downgrade the permission if needed
                    let new_min = kind.minimum(related.minimum).unwrap();
                    if new_min != related.minimum {
                        self.insert(joinable_place, new_min);
                    }
                }
                PlaceOrdering::Equal => {
                    // Downgrade the permission if needed
                    let new_min = kind.minimum(related.minimum).unwrap();
                    if new_min != related.minimum {
                        changed = true;
                        self.insert(place, new_min);
                    }
                }
                PlaceOrdering::Suffix => {
                    // Downgrade the permission if needed
                    for &(p, k) in &related.from {
                        let new_min = kind.minimum(k).unwrap();
                        if new_min != k {
                            changed = true;
                            self.insert(p, new_min);
                        }
                    }
                }
                PlaceOrdering::Both => {
                    changed = true;

                    // Downgrade the permission if needed
                    let min = kind.minimum(related.minimum).unwrap();
                    for &(p, k) in &related.from {
                        let new_min = min.minimum(k).unwrap();
                        if new_min != k {
                            self.insert(p, new_min);
                        }
                    }
                    let cp = repacker.common_prefix(related.from[0].0, place);
                    self.pack(related.get_from(), cp, min, repacker);
                }
            }
        }
        changed
    }
}
