// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::middle::mir::Local;

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections, Fpcs, RepackOp},
    utils::{LocalMutationIsAllowed, Place, PlaceOrdering, PlaceRepacker},
};
use std::fmt::Debug;

impl<'tcx> Fpcs<'_, 'tcx> {
    #[tracing::instrument(name = "Fpcs::requires_unalloc", level = "trace")]
    pub(crate) fn requires_unalloc(&mut self, local: Local) {
        assert!(
            self.summary[local].is_unallocated(),
            "local: {local:?}, fpcs: {self:?}\n"
        );
    }
    #[tracing::instrument(name = "Fpcs::requires_unalloc_or_uninit", level = "trace")]
    pub(crate) fn requires_unalloc_or_uninit(&mut self, local: Local) {
        if !self.summary[local].is_unallocated() {
            self.requires_write(local)
        } else {
            self.repackings.push(RepackOp::IgnoreStorageDead(local))
        }
    }
    #[tracing::instrument(name = "Fpcs::requires_read", level = "trace")]
    pub(crate) fn requires_read(&mut self, place: impl Into<Place<'tcx>> + Debug) {
        self.requires(place, CapabilityKind::Exclusive)
    }
    /// May obtain write _or_ exclusive, if one should only have write afterwards,
    /// make sure to also call `ensures_write`!
    #[tracing::instrument(name = "Fpcs::requires_write", level = "trace")]
    pub(crate) fn requires_write(&mut self, place: impl Into<Place<'tcx>> + Debug) {
        let place = place.into();
        // Cannot get write on a shared ref
        assert!(place
            .is_mutable(LocalMutationIsAllowed::Yes, self.repacker)
            .is_ok());
        self.requires(place, CapabilityKind::Write)
    }
    #[tracing::instrument(name = "Fpcs::requires_write", level = "trace")]
    pub(crate) fn requires_exclusive(&mut self, place: impl Into<Place<'tcx>> + Debug) {
        let place = place.into();
        // Cannot get exclusive on a shared ref
        assert!(!place.projects_shared_ref(self.repacker));
        self.requires(place, CapabilityKind::Exclusive)
    }
    fn requires(&mut self, place: impl Into<Place<'tcx>>, cap: CapabilityKind) {
        let place = place.into();
        let cp: &mut CapabilityProjections = self.summary[place.local].get_allocated_mut();
        let ops = cp.repack(place, self.repacker);
        self.repackings.extend(ops);
        let kind = cp[&place];
        if cap.is_write() {
            // Requires write should deinit an exclusive
            cp.insert(place, cap);
            if kind != cap {
                self.repackings.push(RepackOp::Weaken(place, kind, cap));
            }
        };
        assert!(kind >= cap);
    }

    pub(crate) fn ensures_unalloc(&mut self, local: Local) {
        self.summary[local] = CapabilityLocal::Unallocated;
    }
    pub(crate) fn ensures_allocates(&mut self, local: Local) {
        assert_eq!(self.summary[local], CapabilityLocal::Unallocated);
        self.summary[local] = CapabilityLocal::Allocated(CapabilityProjections::new_uninit(local));
    }
    fn ensures_alloc(&mut self, place: impl Into<Place<'tcx>>, cap: CapabilityKind) {
        let place = place.into();
        let cp: &mut CapabilityProjections = self.summary[place.local].get_allocated_mut();
        cp.update_cap(place, cap);
    }
    pub(crate) fn ensures_exclusive(&mut self, place: impl Into<Place<'tcx>>) {
        self.ensures_alloc(place, CapabilityKind::Exclusive)
    }
    pub(crate) fn ensures_shallow_exclusive(&mut self, place: impl Into<Place<'tcx>>) {
        self.ensures_alloc(place, CapabilityKind::ShallowExclusive)
    }
    pub(crate) fn ensures_write(&mut self, place: impl Into<Place<'tcx>>) {
        let place = place.into();
        // Cannot get uninitialize behind a ref (actually drop does this)
        assert!(place.can_deinit(self.repacker), "{place:?}");
        self.ensures_alloc(place, CapabilityKind::Write)
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    pub(super) fn repack(
        &mut self,
        to: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<RepackOp<'tcx>> {
        let related = self.find_all_related(to, None);
        match related.relation {
            PlaceOrdering::Prefix => self.expand(related.get_only_from(), related.to, repacker),
            PlaceOrdering::Equal => Vec::new(),
            PlaceOrdering::Suffix => self.collapse(related.get_from(), related.to, repacker),
            PlaceOrdering::Both => {
                let cp = related.common_prefix(to);
                // Collapse
                let mut ops = self.collapse(related.get_from(), cp, repacker);
                // Expand
                let unpacks = self.expand(cp, related.to, repacker);
                ops.extend(unpacks);
                ops
            }
        }
    }
}
