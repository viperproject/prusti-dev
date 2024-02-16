// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::cell::Cell;
use std::rc::Rc;

use prusti_rustc_interface::{
    dataflow::{Analysis, AnalysisDomain},
    index::{Idx, IndexVec},
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Location, Promoted,
            Statement, Terminator, TerminatorEdges, RETURN_PLACE, START_BLOCK,
        },
        ty::TyCtxt,
    },
};

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, FreePlaceCapabilitySummary, engine::FpcsEngine},
    utils::PlaceRepacker, coupling_graph::{CgContext, engine::CgEngine, coupling::CouplingOp},
};

use super::domain::PlaceCapabilitySummary;

pub struct PcsEngine<'a, 'tcx> {
    pub(crate) cgx: Rc<CgContext<'a, 'tcx>>,
    block: Cell<BasicBlock>,

    pub(crate) fpcs: FpcsEngine<'a, 'tcx>,
    pub(crate) cg: CgEngine<'a, 'tcx>,
}
impl<'a, 'tcx> PcsEngine<'a, 'tcx> {
    pub fn new(cgx: CgContext<'a, 'tcx>) -> Self {
        let cgx = Rc::new(cgx);
        let fpcs = FpcsEngine(cgx.rp);
        let cg = CgEngine::new(cgx.clone(), false);
        Self {
            cgx,
            block: Cell::new(START_BLOCK),
            fpcs,
            cg,
        }
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for PcsEngine<'a, 'tcx> {
    type Domain = PlaceCapabilitySummary<'a, 'tcx>;
    const NAME: &'static str = "pcs";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        let block = self.block.get();
        self.block.set(block.plus(1));
        PlaceCapabilitySummary::new(self.cgx.clone(), block)
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        self.block.set(START_BLOCK);
        state.fpcs.initialize_as_start_block();
        state.cg.initialize_start_block(&self.cgx);
    }
}

impl<'a, 'tcx> Analysis<'tcx> for PcsEngine<'a, 'tcx> {
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.cg.apply_before_statement_effect(&mut state.cg, statement, location);
        for c in &state.cg.couplings {
            match c {
                CouplingOp::Add(_) => todo!(),
                CouplingOp::Activate(_) => todo!(),
                CouplingOp::Remove(from, _) => {
                    state.fpcs.after.fold_up_to(self.cgx.rp, *from);
                }
            }
        }
        self.fpcs.apply_before_statement_effect(&mut state.fpcs, statement, location);
    }
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.cg.apply_statement_effect(&mut state.cg, statement, location);
        self.fpcs.apply_statement_effect(&mut state.fpcs, statement, location);
    }
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        self.cg.apply_before_terminator_effect(&mut state.cg, terminator, location);
        self.fpcs.apply_before_terminator_effect(&mut state.fpcs, terminator, location);
    }
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        self.cg.apply_terminator_effect(&mut state.cg, terminator, location);
        self.fpcs.apply_terminator_effect(&mut state.fpcs, terminator, location);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}
