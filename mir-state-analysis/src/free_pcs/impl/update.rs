// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{data_structures::fx::FxHashSet, middle::mir::Local};

use crate::{
    utils::PlaceRepacker, CapabilityKind, CapabilityLocal, CapabilityProjections, Fpcs, Place,
    PlaceOrdering, RelatedSet, RepackOp,
};

impl<'tcx> Fpcs<'_, 'tcx> {
    pub(crate) fn requires_unalloc(&mut self, local: Local) {
        assert!(
            self.summary[local].is_unallocated(),
            "local: {local:?}, fpcs: {self:?}\n"
        );
    }
    pub(crate) fn requires_unalloc_or_uninit(&mut self, local: Local) {
        if !self.summary[local].is_unallocated() {
            self.requires_write(local)
        }
    }
    pub(crate) fn requires_read(&mut self, place: impl Into<Place<'tcx>>) {
        self.requires(place, CapabilityKind::Read)
    }
    /// May obtain write _or_ exclusive, if one should only have write afterwards,
    /// make sure to also call `ensures_write`!
    pub(crate) fn requires_write(&mut self, place: impl Into<Place<'tcx>>) {
        self.requires(place, CapabilityKind::Write)
    }
    pub(crate) fn requires_exclusive(&mut self, place: impl Into<Place<'tcx>>) {
        self.requires(place, CapabilityKind::Exclusive)
    }
    fn requires(&mut self, place: impl Into<Place<'tcx>>, cap: CapabilityKind) {
        let place = place.into();
        let cp: &mut CapabilityProjections = self.summary[place.local].get_allocated_mut();
        let ops = cp.repack(place, self.repacker);
        self.repackings.extend(ops);
        let kind = (*cp)[&place];
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
        let old = cp.insert(place, cap);
        assert!(old.is_some());
    }
    pub(crate) fn ensures_exclusive(&mut self, place: impl Into<Place<'tcx>>) {
        self.ensures_alloc(place, CapabilityKind::Exclusive)
    }
    pub(crate) fn ensures_write(&mut self, place: impl Into<Place<'tcx>>) {
        self.ensures_alloc(place, CapabilityKind::Write)
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    fn repack(
        &mut self,
        to: Place<'tcx>,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Vec<RepackOp<'tcx>> {
        let related = self.find_all_related(to, None);
        match related.relation {
            PlaceOrdering::Prefix => self
                .unpack_ops(related.from[0].0, related.to, related.minimum, repacker)
                .collect(),
            PlaceOrdering::Equal => Vec::new(),
            PlaceOrdering::Suffix => self
                .pack_ops(related.get_from(), related.to, related.minimum, repacker)
                .collect(),
            PlaceOrdering::Both => {
                let cp = related.from[0].0.common_prefix(to, repacker);
                // Pack
                let mut ops = self.weaken(&related);
                let packs = self.pack_ops(related.get_from(), cp, related.minimum, repacker);
                ops.extend(packs);
                // Unpack
                let unpacks = self.unpack_ops(cp, related.to, related.minimum, repacker);
                ops.extend(unpacks);
                ops
            }
        }
    }
    pub(crate) fn unpack_ops(
        &mut self,
        from: Place<'tcx>,
        to: Place<'tcx>,
        kind: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> impl Iterator<Item = RepackOp<'tcx>> {
        self.unpack(from, to, repacker)
            .into_iter()
            .map(move |(f, t)| RepackOp::Unpack(f, t, kind))
    }
    pub(crate) fn pack_ops(
        &mut self,
        from: FxHashSet<Place<'tcx>>,
        to: Place<'tcx>,
        perm: CapabilityKind,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> impl Iterator<Item = RepackOp<'tcx>> {
        self.pack(from, to, perm, repacker)
            .into_iter()
            .map(move |(f, t)| RepackOp::Pack(f, t, perm))
    }

    pub(crate) fn weaken(&mut self, related: &RelatedSet<'tcx>) -> Vec<RepackOp<'tcx>> {
        let mut ops = Vec::new();
        let more_than_min = related.from.iter().filter(|(_, k)| *k != related.minimum);
        // TODO: This will replace `PermissionKind::Exclusive` with `PermissionKind::Shared`
        // the exclusive permission will never be able to be recovered anymore!
        for &(p, k) in more_than_min {
            let old = self.insert(p, related.minimum);
            assert_eq!(old, Some(k));
            ops.push(RepackOp::Weaken(p, k, related.minimum));
        }
        ops
    }
}
