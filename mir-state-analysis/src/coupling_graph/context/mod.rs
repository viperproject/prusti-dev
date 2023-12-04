// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{cell::RefCell, fmt};

use self::{
    outlives_info::OutlivesInfo, region_info::RegionInfo, shared_borrow_set::SharedBorrowSet,
};
use crate::{
    r#loop::LoopAnalysis,
    utils::{Place, PlaceRepacker},
};
use prusti_rustc_interface::{
    borrowck::consumers::BodyWithBorrowckFacts,
    borrowck::consumers::{BorrowIndex, Borrows, OutlivesConstraint},
    data_structures::fx::FxHashMap,
    dataflow::{Analysis, ResultsCursor},
    index::IndexVec,
    middle::{
        mir::{Body, Location, Promoted, RETURN_PLACE},
        ty::{RegionVid, TyCtxt},
    },
};

pub(crate) mod shared_borrow_set;
pub(crate) mod region_info;
pub(crate) mod outlives_info;

pub struct CgContext<'a, 'tcx> {
    pub rp: PlaceRepacker<'a, 'tcx>,
    pub mir: &'a BodyWithBorrowckFacts<'tcx>,

    pub sbs: SharedBorrowSet<'tcx>,
    // pub region_map: FxHashMap<RegionVid, PlaceRegion<'tcx>>,
    pub loops: LoopAnalysis,

    pub region_info: RegionInfo<'tcx>,
    pub outlives_info: OutlivesInfo<'tcx>,
}

impl fmt::Debug for CgContext<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CgContext")
            .field("sbs", &self.sbs)
            .field("region_info", &self.region_info)
            .field("outlives_info", &self.outlives_info)
            .finish()
    }
}

impl<'a, 'tcx> CgContext<'a, 'tcx> {
    #[tracing::instrument(name = "CgContext::new", level = "debug", skip_all, ret)]
    pub fn new(
        tcx: TyCtxt<'tcx>,
        mir: &'a BodyWithBorrowckFacts<'tcx>,
    ) -> Self {
        let borrow_set = &mir.borrow_set;
        let sbs = SharedBorrowSet::build(tcx, &mir.body, borrow_set);
        let rp = PlaceRepacker::new(&mir.body, &mir.promoted, tcx);
        let input_facts = mir.input_facts.as_ref().unwrap();
        let loops = LoopAnalysis::find_loops(&mir.body);

        let region_info = RegionInfo::new(rp, input_facts, mir.region_inference_context.as_ref(), borrow_set.as_ref(), &sbs);
        let outlives_info = OutlivesInfo::new(input_facts, mir.region_inference_context.as_ref(), borrow_set.as_ref(), &region_info);

        Self {
            rp,
            mir,
            sbs,
            loops,
            region_info,
            outlives_info,
        }
    }
}
