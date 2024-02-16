// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections},
    utils::{LocalMutationIsAllowed, Place, PlaceOrdering, PlaceRepacker},
};

use super::{CapabilitySummary, triple::{Condition, Triple}};

impl<'tcx> CapabilitySummary<'tcx> {
    pub(crate) fn requires(&mut self, cond: Condition<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) {
        match cond {
            Condition::Unchanged => {}
            Condition::Unalloc(_) => {},
            Condition::AllocateOrDeallocate(local) => {
                match &mut self[local] {
                    cap@CapabilityLocal::Unallocated => {
                        // A bit of an unusual case: we're at a StorageDead but
                        // already deallocated. Allocate now so that the
                        // precondition of SD can be met, but we'll catch this in
                        // `bridge` and emit a IgnoreSD op.
                        *cap = CapabilityLocal::Allocated(CapabilityProjections::new_uninit(local));
                    }
                    CapabilityLocal::Allocated(_) =>
                        self.requires(Condition::Capability(local.into(), CapabilityKind::Write), repacker),
                }
            }
            Condition::Capability(place, cap) => {
                let cp = self[place.local].get_allocated_mut();
                cp.repack(place, repacker);
                if cp[&place] > cap {
                    // Requires write should deinit an exclusive
                    cp.insert(place, cap);
                };
            }
        }
    }
    pub(crate) fn ensures(&mut self, t: Triple<'tcx>, repacker: PlaceRepacker<'_, 'tcx>) {
        match t.pre {
            Condition::Unchanged => {}
            Condition::Unalloc(local) => {
                assert!(self[local].is_unallocated(), "local: {local:?}, fpcs: {self:?}\n");
            }
            Condition::AllocateOrDeallocate(local) => {
                assert_eq!(self[local].get_allocated_mut()[&local.into()], CapabilityKind::Write);
            }
            Condition::Capability(place, cap) => {
                match cap {
                    CapabilityKind::Write => {
                        // Cannot get write on a shared ref
                        debug_assert!(place
                            .is_mutable(LocalMutationIsAllowed::Yes, repacker)
                            .is_ok());
                    }
                    CapabilityKind::Exclusive => {
                        // Cannot get exclusive on a shared ref
                        assert!(!place.projects_shared_ref(repacker));
                    }
                    CapabilityKind::ShallowExclusive => unreachable!(),
                }

                let cp = self[place.local].get_allocated_mut();
                assert_eq!(cp[&place], cap); // TODO: is this too strong for shallow exclusive?
            }
        }
        match t.post {
            Condition::Unchanged => {}
            Condition::Unalloc(local) => {
                self[local] = CapabilityLocal::Unallocated;
            }
            Condition::AllocateOrDeallocate(local) => {
                self[local] = CapabilityLocal::Allocated(CapabilityProjections::new_uninit(local));
            }
            Condition::Capability(place, cap) => {
                self[place.local].get_allocated_mut().update_cap(place, cap);
            }
        }
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    #[tracing::instrument(
        name = "CapabilityProjections::repack",
        level = "trace",
        skip(repacker),
        ret
    )]
    pub(super) fn repack(
        &mut self,
        to: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) {
        let related = self.find_all_related(to, None);
        match related.relation {
            PlaceOrdering::Prefix => {
                self.expand(related.get_only_from(), related.to, repacker);
            }
            PlaceOrdering::Equal => (),
            PlaceOrdering::Suffix => {
                self.collapse(related.get_from(), related.to, repacker);
            }
            PlaceOrdering::Both => {
                let cp = related.common_prefix(to);
                // Collapse
                self.collapse(related.get_from(), cp, repacker);
                // Expand
                self.expand(cp, related.to, repacker);
            }
        }
    }
}
