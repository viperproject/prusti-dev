// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilityProjections, CapabilitySummary, RepackOp,
    },
    utils::{PlaceOrdering, PlaceRepacker},
};

pub trait RepackingBridgeSemiLattice<'tcx> {
    fn bridge(&self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<RepackOp<'tcx>>;
}
impl<'tcx> RepackingBridgeSemiLattice<'tcx> for CapabilitySummary<'tcx> {
    #[tracing::instrument(name = "CapabilitySummary::bridge", level = "trace", skip(repacker))]
    fn bridge(&self, other: &Self, repacker: PlaceRepacker<'_, 'tcx>) -> Vec<RepackOp<'tcx>> {
        let mut repacks = Vec::new();
        for (l, from) in self.iter_enumerated() {
            let local_repacks = from.bridge(&other[l], repacker);
            repacks.extend(local_repacks);
        }
        repacks
    }
}

impl<'tcx> RepackingBridgeSemiLattice<'tcx> for CapabilityLocal<'tcx> {
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
            (CapabilityLocal::Unallocated, CapabilityLocal::Allocated(cps)) => {
                // A bit of an unusual case, should happen only when we
                // "allocated" a local to allow it to immediately be
                // StorageDead-ed. In this case we should ignore the SD.
                assert_eq!(cps[&cps.get_local().into()], CapabilityKind::Write);
                vec![RepackOp::IgnoreStorageDead(cps.get_local())]
            }
        }
    }
}

impl<'tcx> RepackingBridgeSemiLattice<'tcx> for CapabilityProjections<'tcx> {
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
