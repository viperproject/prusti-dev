// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::dataflow::JoinSemiLattice;

use crate::{
    utils::PlaceRepacker, CapabilityKind, CapabilityLocal, CapabilityProjections,
    CapabilitySummary, Fpcs, PlaceOrdering, RepackOp,
};

impl JoinSemiLattice for Fpcs<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        self.summary.join(&other.summary, self.repacker)
    }
}

pub trait RepackingJoinSemiLattice<'tcx> {
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> bool;
    fn bridge(&self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<RepackOp<'tcx>>;
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
    fn bridge(&self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<RepackOp<'tcx>> {
        let mut repacks = Vec::new();
        for (l, to) in self.iter_enumerated() {
            let local_repacks = to.bridge(&other[l], repacker);
            repacks.extend(local_repacks);
        }
        repacks
    }
}

impl<'tcx> RepackingJoinSemiLattice<'tcx> for CapabilityLocal<'tcx> {
    #[tracing::instrument(name = "CapabilityLocal::join", level = "debug", skip(repacker))]
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
    fn bridge(&self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<RepackOp<'tcx>> {
        match (self, other) {
            (CapabilityLocal::Unallocated, CapabilityLocal::Unallocated) => Vec::new(),
            (CapabilityLocal::Allocated(to_places), CapabilityLocal::Allocated(from_places)) => {
                to_places.bridge(from_places, repacker)
            }
            (CapabilityLocal::Allocated(cps), CapabilityLocal::Unallocated) => {
                // TODO: remove need for clone
                let mut cps = cps.clone();
                let local = cps.get_local();
                let mut repacks = Vec::new();
                for (&p, k) in cps.iter_mut() {
                    if *k > CapabilityKind::Write {
                        repacks.push(RepackOp::Weaken(p, *k, CapabilityKind::Write));
                        *k = CapabilityKind::Write;
                    }
                }
                if !cps.contains_key(&local.into()) {
                    let packs = cps.pack_ops(
                        cps.keys().copied().collect(),
                        local.into(),
                        CapabilityKind::Write,
                        repacker,
                    );
                    repacks.extend(packs);
                };
                repacks.push(RepackOp::DeallocForCleanup(local));
                repacks
            }
            (CapabilityLocal::Unallocated, CapabilityLocal::Allocated(..)) => unreachable!(),
        }
    }
}

impl<'tcx> RepackingJoinSemiLattice<'tcx> for CapabilityProjections<'tcx> {
    #[tracing::instrument(name = "CapabilityProjections::join", level = "trace", skip(repacker))]
    fn join(&mut self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> bool {
        let mut changed = false;
        for (&place, &kind) in &**other {
            let related = self.find_all_related(place, None);
            match related.relation {
                PlaceOrdering::Prefix => {
                    changed = true;

                    let from = related.from[0].0;
                    let joinable_place = from.joinable_to(place, repacker);
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
                    let cp = related.from[0].0.common_prefix(place, repacker);
                    self.pack(related.get_from(), cp, min, repacker);
                }
            }
        }
        changed
    }
    fn bridge(&self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<RepackOp<'tcx>> {
        // TODO: remove need for clone
        let mut cps = self.clone();

        let mut repacks = Vec::new();
        for (&place, &kind) in &**other {
            let related = cps.find_all_related(place, None);
            match related.relation {
                PlaceOrdering::Prefix => {
                    let from = related.from[0].0;
                    // TODO: remove need for clone
                    let unpacks = cps.unpack_ops(from, place, related.minimum, repacker);
                    repacks.extend(unpacks);

                    // Downgrade the permission if needed
                    let new_min = kind.minimum(related.minimum).unwrap();
                    if new_min != related.minimum {
                        cps.insert(place, new_min);
                        repacks.push(RepackOp::Weaken(place, related.minimum, new_min));
                    }
                }
                PlaceOrdering::Equal => {
                    // Downgrade the permission if needed
                    let new_min = kind.minimum(related.minimum).unwrap();
                    if new_min != related.minimum {
                        cps.insert(place, new_min);
                        repacks.push(RepackOp::Weaken(place, related.minimum, new_min));
                    }
                }
                PlaceOrdering::Suffix => {
                    // Downgrade the permission if needed
                    for &(p, k) in &related.from {
                        let new_min = kind.minimum(k).unwrap();
                        if new_min != k {
                            cps.insert(p, new_min);
                            repacks.push(RepackOp::Weaken(p, k, new_min));
                        }
                    }
                    let packs =
                        cps.pack_ops(related.get_from(), related.to, related.minimum, repacker);
                    repacks.extend(packs);
                }
                PlaceOrdering::Both => unreachable!(),
            }
        }
        repacks
    }
}
