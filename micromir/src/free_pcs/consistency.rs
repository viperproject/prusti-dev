// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{utils::PlaceRepacker, Summary, CapabilityLocal, CapabilityProjections, Place};

trait CapabilityConistency<'tcx> {
    fn check(&self, repacker: PlaceRepacker<'_, 'tcx>);
}

impl<'tcx, T: CapabilityConistency<'tcx>> CapabilityConistency<'tcx> for Summary<T> {
    fn check(&self, repacker: PlaceRepacker<'_, 'tcx>) {
        for p in self.iter() {
            p.check(repacker)
        }
    }
}

impl<'tcx> CapabilityConistency<'tcx> for CapabilityLocal<'tcx> {
    fn check(&self, repacker: PlaceRepacker<'_, 'tcx>) {
        match self {
            CapabilityLocal::Unallocated => {}
            CapabilityLocal::Allocated(cp) => cp.check(repacker),
        }
    }
}

impl<'tcx> CapabilityConistency<'tcx> for CapabilityProjections<'tcx> {
    fn check(&self, repacker: PlaceRepacker<'_, 'tcx>) {
        // All keys unrelated to each other
        let keys = self.keys().copied().collect::<Vec<_>>();
        for (i, p1) in keys.iter().enumerate() {
            for p2 in keys[i + 1..].iter() {
                assert!(!p1.related_to(*p2), "{p1:?} {p2:?}",);
            }
        }
        // Can always pack up to the root
        let root: Place = self.get_local().into();
        let mut keys = self.keys().copied().collect();
        repacker.collapse(root, &mut keys);
        assert!(keys.is_empty());
    }
}
