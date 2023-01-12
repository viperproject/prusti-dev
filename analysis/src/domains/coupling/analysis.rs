// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine},
    domains::CouplingState,
    PointwiseState,
};
use prusti_rustc_interface::{
    borrowck::BodyWithBorrowckFacts,
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, ty::TyCtxt},
    span::def_id::DefId,
};

pub struct CouplingAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'mir, 'tcx: 'mir> CouplingAnalysis<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> Self {
        CouplingAnalysis {
            tcx,
            def_id,
            body_with_facts,
        }
    }
}

impl<'mir, 'tcx: 'mir> FixpointEngine<'mir, 'tcx> for CouplingAnalysis<'mir, 'tcx> {
    type State = CouplingState<'tcx>;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        &self.body_with_facts.body
    }

    fn new_bottom(&self) -> Self::State {
        todo!()
    }

    fn new_initial(&self) -> Self::State {
        todo!()
    }

    fn need_to_widen(counter: u32) -> bool {
        // todo: remove this.
        assert!(counter < 2);
        false
    }

    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()> {
        todo!()
    }

    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        todo!()
    }
}

// todo: Put
impl<'mir, 'tcx: 'mir> PointwiseState<'mir, 'tcx, CouplingState<'tcx>> {}
