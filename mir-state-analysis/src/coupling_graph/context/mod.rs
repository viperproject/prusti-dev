// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{fmt, cell::RefCell};

use crate::{utils::{PlaceRepacker, Place}, r#loop::LoopAnalysis};
use self::{shared_borrow_set::SharedBorrowSet, region_place::Perms};
use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    borrowck::consumers::{Borrows, BorrowIndex, OutlivesConstraint},
    dataflow::{Analysis, ResultsCursor},
    data_structures::fx::{FxIndexMap, FxHashMap},
    middle::{mir::{Body, Location, RETURN_PLACE}, ty::{RegionVid, TyCtxt}},
};

pub(crate) mod shared_borrow_set;
pub(crate) mod region_place;

pub struct CgContext<'a, 'tcx> {
    pub rp: PlaceRepacker<'a, 'tcx>,
    pub facts: &'a BorrowckFacts,
    pub facts2: &'a BorrowckFacts2<'tcx>,

    pub sbs: SharedBorrowSet<'tcx>,
    pub region_map: FxHashMap<RegionVid, Perms<'tcx>>,
    pub loops: LoopAnalysis,
}

impl fmt::Debug for CgContext<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CgContext").field("sbs", &self.sbs).field("region_map", &self.region_map).finish()
    }
}

impl<'a, 'tcx> CgContext<'a, 'tcx> {
    #[tracing::instrument(name = "CgContext::new", level = "debug", skip_all, ret)]
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        facts: &'a BorrowckFacts,
        facts2: &'a BorrowckFacts2<'tcx>
    ) -> Self {
        let borrow_set = &facts2.borrow_set;
        let sbs = SharedBorrowSet::build(tcx, body, borrow_set);
        let rp = PlaceRepacker::new(body, tcx);
        let input_facts = facts.input_facts.borrow();
        let region_map = Perms::region_place_map(
            &input_facts.as_ref().unwrap().use_of_var_derefs_origin,
            borrow_set,
            &sbs,
            rp,
        );
        let loops = LoopAnalysis::find_loops(body);

        Self {
            rp,
            facts,
            facts2,
            sbs,
            region_map,
            loops,
        }
    }

    pub fn get_constraints_for_loc(&self, location: Option<Location>) -> impl Iterator<Item = OutlivesConstraint<'tcx>> + '_ {
        self.facts2.region_inference_context.outlives_constraints().filter(
            move |c| c.locations.from_location() == location
        )
    }

    /// This is the hack we use to make a `fn foo<'a>(x: &'a _, y: &'a _, ...) -> &'a _` look like
    /// `fn foo<'a: 'c, 'b: 'c, 'c>(x: &'a _, y: &'b _, ...) -> &'c _` to the analysis.
    #[tracing::instrument(name = "ignore_outlives", level = "debug", skip(self), ret)]
    pub fn ignore_outlives(&self, c: OutlivesConstraint<'tcx>) -> bool {
        let arg_count = self.rp.body().arg_count;
        let sup = self.region_map.get(&c.sup);
        let sub = self.region_map.get(&c.sub);
        match (sup, sub) {
            // If `projects_exactly_one_deref` then it must be the `'a` region of a `x: &'a ...`, rather than being nested deeper withing the local
            (_, Some(sub)) => {
                sub.place.projects_exactly_one_deref()
                    && sub.place.local.index() <= arg_count
                    && sub.place.local != RETURN_PLACE
            }
            // (Some(sup), Some(sub)) => {
            //     if !(sup.place.projects_exactly_one_deref()
            //         && sub.place.projects_exactly_one_deref()
            //         && sup.place.local.index() <= arg_count
            //         && sub.place.local.index() <= arg_count) {
            //         return false;
            //     }
            //     debug_assert_ne!(sup.place.local, sub.place.local);
            //     sub.place.local != RETURN_PLACE
            // }
            _ => false,
        }
    }
}
