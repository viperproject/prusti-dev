// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::AnalysisResult,
    domains::{
        DefinitelyAccessibleState, DefinitelyInitializedAnalysis, MaybeBorrowedAnalysis
    },
    PointwiseState,
};
use rustc_borrowck::BodyWithBorrowckFacts;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;

pub struct DefinitelyAccessibleAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'mir, 'tcx: 'mir> DefinitelyAccessibleAnalysis<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> Self {
        DefinitelyAccessibleAnalysis {
            tcx,
            def_id,
            body_with_facts,
        }
    }

    pub fn run_analysis(
        &self,
    ) -> AnalysisResult<PointwiseState<'mir, 'tcx, DefinitelyAccessibleState>> {
        let definitely_initialized =
            DefinitelyInitializedAnalysis::new(self.tcx, self.def_id, &self.body_with_facts.body);
        let maybe_borrowed = MaybeBorrowedAnalysis::new(self.body_with_facts);
        let analysis_state = PointwiseState::default(&self.body_with_facts.body);
        Ok(analysis_state)
    }
}
