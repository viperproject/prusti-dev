// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, CapabilityProjections, Summary},
    utils::{Place, PlaceRepacker},
};

pub trait CapabilityConistency<'tcx> {
    fn consistency_check(&self, repacker: PlaceRepacker<'_, 'tcx>);
}

impl<'tcx, T: CapabilityConistency<'tcx>> CapabilityConistency<'tcx> for Summary<T> {
    fn consistency_check(&self, repacker: PlaceRepacker<'_, 'tcx>) {
        for p in self.iter() {
            p.consistency_check(repacker)
        }
    }
}

impl<'tcx> CapabilityConistency<'tcx> for CapabilityLocal<'tcx> {
    fn consistency_check(&self, repacker: PlaceRepacker<'_, 'tcx>) {
        match self {
            CapabilityLocal::Unallocated => {}
            CapabilityLocal::Allocated(cp) => cp.consistency_check(repacker),
        }
    }
}

impl<'tcx> CapabilityConistency<'tcx> for CapabilityProjections<'tcx> {
    fn consistency_check(&self, repacker: PlaceRepacker<'_, 'tcx>) {
        // All keys unrelated to each other
        let keys = self.keys().copied().collect::<Vec<_>>();
        for (i, p1) in keys.iter().enumerate() {
            for p2 in keys[i + 1..].iter() {
                assert!(!p1.related_to(*p2), "{p1:?} {p2:?}",);
            }
            // Cannot be inside of uninitialized pointers.
            if !p1.can_deinit(repacker) {
                assert!(matches!(self[p1], CapabilityKind::Exclusive), "{self:?}");
            }
            // Cannot have Read or None here
            assert!(self[p1] >= CapabilityKind::Write);
            // Can only have `ShallowExclusive` for box typed places
            if self[p1].is_shallow_exclusive() {
                assert!(p1.ty(repacker).ty.is_box());
            }
        }
        // Can always pack up to the root
        let root: Place = self.get_local().into();
        let mut keys = self.keys().copied().collect();
        root.collapse(&mut keys, repacker);
        assert!(keys.is_empty());
    }
}
