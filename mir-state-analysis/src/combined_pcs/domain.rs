// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cell::{RefCell, Cell},
    fmt::{Debug, Formatter, Result}, rc::Rc,
};

use derive_more::{Deref, DerefMut};
use prusti_rustc_interface::{
    dataflow::JoinSemiLattice,
    dataflow::fmt::DebugWithContext, index::IndexVec, middle::mir::{BasicBlock, Location, START_BLOCK},
};

use crate::{
    free_pcs::{
        CapabilityLocal, CapabilityProjections, RepackOp, FreePlaceCapabilitySummary, HasFpcs,
    },
    utils::{Place, PlaceRepacker}, coupling_graph::{CgContext, triple::CouplingGraph},
};

use super::PcsEngine;

#[derive(Clone)]
pub struct PlaceCapabilitySummary<'a, 'tcx> {
    pub cgx: Rc<CgContext<'a, 'tcx>>,
    pub block: BasicBlock,

    pub fpcs: FreePlaceCapabilitySummary<'a, 'tcx>,
    pub cg: CouplingGraph<'a, 'tcx>,
}

impl<'a, 'tcx> PlaceCapabilitySummary<'a, 'tcx> {
    pub fn new(cgx: Rc<CgContext<'a, 'tcx>>, block: BasicBlock) -> Self {
        let fpcs = FreePlaceCapabilitySummary::new(cgx.rp);
        let cg = CouplingGraph::new(cgx.clone(), false, block);
        Self { cgx, block, fpcs, cg }
    }
}

impl Eq for PlaceCapabilitySummary<'_, '_> {}
impl PartialEq for PlaceCapabilitySummary<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.fpcs == other.fpcs && self.cg == other.cg
    }
}
impl Debug for PlaceCapabilitySummary<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{:?}\n{:?}", self.fpcs, self.cg)
    }
}

impl JoinSemiLattice for PlaceCapabilitySummary<'_, '_> {
    fn join(&mut self, other: &Self) -> bool {
        let fpcs = self.fpcs.join(&other.fpcs);
        let cg = self.cg.join(&other.cg);
        fpcs || cg
    }
}

impl<'a, 'tcx> DebugWithContext<PcsEngine<'a, 'tcx>> for PlaceCapabilitySummary<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &PcsEngine<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        self.fpcs.fmt_diff_with(&old.fpcs, &ctxt.fpcs, f)
    }
}

// impl<'mir, 'tcx> HasFpcs<'mir, 'tcx> for PlaceCapabilitySummary<'mir, 'tcx> {
//     fn get_curr_fpcs(&self) -> &FreePlaceCapabilitySummary<'mir, 'tcx> {
//         &self.fpcs
//     }
// }
