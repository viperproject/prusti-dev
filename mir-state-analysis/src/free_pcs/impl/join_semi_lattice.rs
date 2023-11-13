// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::dataflow::JoinSemiLattice;

use crate::{
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityProjections, CapabilitySummary, Fpcs, RepackOp,
    },
    utils::{PlaceOrdering, PlaceRepacker},
};

impl JoinSemiLattice for Fpcs<'_, '_> {
    #[tracing::instrument(name = "Fpcs::join", level = "debug")]
    fn join(&mut self, other: &Self) -> bool {
        assert!(!other.bottom);
        if self.bottom {
            self.clone_from(other);
            true
        } else {
            self.summary.join(&other.summary, self.repacker)
        }
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
        for (l, from) in self.iter_enumerated() {
            let local_repacks = from.bridge(&other[l], repacker);
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
            (CapabilityLocal::Allocated(from_places), CapabilityLocal::Allocated(to_places)) => {
                from_places.bridge(to_places, repacker)
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
                    let packs = cps.collapse(cps.keys().copied().collect(), local.into(), repacker);
                    repacks.extend(packs);
                };
                repacks.push(RepackOp::StorageDead(local));
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
            let final_place = match related.relation {
                PlaceOrdering::Prefix => {
                    let from = related.get_only_from();
                    let joinable_place = if self[&from] != CapabilityKind::Exclusive {
                        // One cannot expand a `Write` or a `ShallowInit` capability
                        from
                    } else {
                        from.joinable_to(place)
                    };
                    assert!(from.is_prefix(joinable_place));
                    if joinable_place != from {
                        changed = true;
                        self.expand(from, joinable_place, repacker);
                    }
                    Some(joinable_place)
                }
                PlaceOrdering::Equal => Some(place),
                PlaceOrdering::Suffix => {
                    // Downgrade the permission if needed
                    for &(p, k) in &related.from {
                        // Might not contain key if `p.projects_ptr(repacker)`
                        // returned `Some` in a previous iteration.
                        if !self.contains_key(&p) {
                            continue;
                        }
                        let collapse_to = if kind != CapabilityKind::Exclusive {
                            related.to
                        } else {
                            related.to.joinable_to(p)
                        };
                        if collapse_to != p {
                            changed = true;
                            let mut from = related.get_from();
                            from.retain(|&from| collapse_to.is_prefix(from));
                            self.collapse(from, collapse_to, repacker);
                        }
                        if k > kind {
                            changed = true;
                            self.update_cap(collapse_to, kind);
                        }
                    }
                    None
                }
                PlaceOrdering::Both => {
                    changed = true;

                    let cp = related.common_prefix(place);
                    self.collapse(related.get_from(), cp, repacker);
                    Some(cp)
                }
            };
            if let Some(place) = final_place {
                // Downgrade the permission if needed
                if self[&place] > kind {
                    changed = true;
                    self.update_cap(place, kind);
                }
            }
        }
        changed
    }
    fn bridge(&self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<RepackOp<'tcx>> {
        // TODO: remove need for clone
        let mut from = self.clone();

        let mut repacks = Vec::new();
        for (&place, &kind) in &**other {
            let related = from.find_all_related(place, None);
            match related.relation {
                PlaceOrdering::Prefix => {
                    let from_place = related.get_only_from();
                    // TODO: remove need for clone
                    let unpacks = from.expand(from_place, place, repacker);
                    repacks.extend(unpacks);
                }
                PlaceOrdering::Equal => (),
                PlaceOrdering::Suffix => {
                    let packs = from.collapse(related.get_from(), related.to, repacker);
                    repacks.extend(packs);
                }
                PlaceOrdering::Both => unreachable!("{self:?}\n{from:?}\n{other:?}\n{related:?}"),
            }
            // Downgrade the permission if needed
            let curr = from[&place];
            if curr != kind {
                assert!(curr > kind);
                from.insert(place, kind);
                repacks.push(RepackOp::Weaken(place, curr, kind));
            }
        }
        repacks
    }
}
