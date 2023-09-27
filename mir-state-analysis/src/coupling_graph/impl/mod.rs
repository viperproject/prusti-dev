// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::utils::{PlaceRepacker, Place};
use self::{shared_borrow_set::SharedBorrowSet, region_place::Perms};
use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
    middle::{mir::Body, ty::{RegionVid, TyCtxt}},
};

pub(crate) mod engine;
pub(crate) mod cg;
pub(crate) mod join_semi_lattice;
pub(crate) mod shared_borrow_set;
pub(crate) mod region_place;
mod dot;

pub struct CgContext<'a, 'tcx> {
    pub rp: PlaceRepacker<'a, 'tcx>,
    pub sbs: SharedBorrowSet<'tcx>,
    pub region_map: FxHashMap<RegionVid, Perms<'tcx>>,
}

impl<'a, 'tcx> CgContext<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        facts: &'a BorrowckFacts,
        facts2: &'a BorrowckFacts2<'tcx>
    ) -> Self {
        let sbs = SharedBorrowSet::build(tcx, body, &facts2.borrow_set);
        let rp = PlaceRepacker::new(body, tcx);
        let input_facts = facts.input_facts.borrow();
        let region_map = Perms::region_place_map(
            &input_facts.as_ref().unwrap().use_of_var_derefs_origin,
            &facts2.borrow_set,
            &sbs,
            rp,
        );
        Self {
            rp,
            sbs,
            region_map,
        }
    }
}
