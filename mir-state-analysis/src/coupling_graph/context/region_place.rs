// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use prusti_rustc_interface::{
    borrowck::{
        borrow_set::{BorrowData, BorrowSet, LocalsStateAtExit, TwoPhaseActivation},
        consumers::{BorrowIndex, PlaceExt},
    },
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    dataflow::fmt::DebugWithContext,
    index::{bit_set::BitSet, IndexVec},
    middle::{
        mir::{
            traversal, visit::Visitor, Body, ConstraintCategory, Local, Location, Rvalue,
            RETURN_PLACE,
        },
        ty::{RegionVid, TyKind},
    },
};

use crate::utils::{display::PlaceDisplay, Place, PlaceRepacker};

use super::shared_borrow_set::SharedBorrowSet;

#[derive(Clone)]
pub struct PlaceRegion<'tcx> {
    pub place: Place<'tcx>,
    pub region: Option<RegionVid>,
    pub pretty: PlaceDisplay<'tcx>,
}

impl Debug for PlaceRegion<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let hint = if self.pretty.is_user() {
            format!(" <<{:?}>>", self.pretty)
        } else {
            String::new()
        };
        match self.region {
            Some(r) => write!(f, "AllIn({r:?}, {:?}{hint})", self.place),
            None => write!(f, "{:?}{hint}", self.place),
        }
    }
}

impl<'tcx> PlaceRegion<'tcx> {
    pub fn region_place_map(
        use_of_var_derefs_origin: &Vec<(Local, RegionVid)>,
        borrows: &BorrowSet<'tcx>,
        shared_borrows: &SharedBorrowSet<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> FxHashMap<RegionVid, PlaceRegion<'tcx>> {
        let mut map = FxHashMap::default();
        for &(l, r) in use_of_var_derefs_origin {
            let place = l.into();
            let perm = if let Some(place) = Self::try_make_precise(place, r, rp) {
                PlaceRegion {
                    place,
                    region: None,
                    pretty: place.to_string(rp),
                }
            } else {
                PlaceRegion {
                    place,
                    region: Some(r),
                    pretty: place.to_string(rp),
                }
            };
            let existing = map.insert(r, perm);
            assert!(existing.is_none(), "{existing:?} vs {:?}", map[&r]);
        }
        for data in shared_borrows
            .location_map
            .values()
            .chain(borrows.location_map.values())
        {
            let place = data.borrowed_place.into();
            let perm = PlaceRegion {
                place,
                region: None,
                pretty: place.to_string(rp),
            };
            let existing = map.insert(data.region, perm);
            assert!(
                existing.is_none(),
                "{existing:?} vs {:?}",
                map[&data.region]
            );
        }
        map
    }

    fn try_make_precise(
        mut p: Place<'tcx>,
        r: RegionVid,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> Option<Place<'tcx>> {
        let mut ty = p.ty(rp).ty;
        while let TyKind::Ref(rr, inner_ty, _) = *ty.kind() {
            ty = inner_ty;
            p = p.mk_deref(rp);
            if rr.is_var() && rr.as_var() == r {
                return Some(p);
            }
        }
        None
    }
}
