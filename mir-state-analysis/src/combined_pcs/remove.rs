// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::middle::{
    mir::PlaceRef,
    ty::RegionVid,
};

use crate::{free_pcs::{CapabilitySummary, CapabilityLocal, CapabilityProjections}, utils::PlaceRepacker};

impl<'tcx> CapabilitySummary<'tcx> {
    pub fn fold_up_to(&mut self, rp: PlaceRepacker<'_, 'tcx>, r: RegionVid) {
        for local in self.iter_mut() {
            if let CapabilityLocal::Allocated(cap) = local {
                cap.fold_up_to(rp, r);
            }
        }
    }
}

impl<'tcx> CapabilityProjections<'tcx> {
    pub fn fold_up_to(&mut self, rp: PlaceRepacker<'_, 'tcx>, r: RegionVid) {
        let to_fold_up: Vec<_> = self.keys().flat_map(|place| {
            place.projection_refs(rp).find_map(|(ref_info, projs)|
                ref_info.filter(|(or, _, _)| or.as_var() == r).map(|_| projs)
            ).map(|projection| PlaceRef { local: place.local, projection })
        }).collect();
        for place in to_fold_up {
            let place = place.into();
            if !self.contains_key(&place) {
                let related = self.find_all_related(place, Some(crate::utils::PlaceOrdering::Suffix));
                self.collapse(related.get_from(), place, rp);
            }
        }
    }
}
