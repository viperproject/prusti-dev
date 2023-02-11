// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::facts::FactTable;
use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine},
    PointwiseState,
};

use crate::domains::coupling::CouplingState;
use prusti_rustc_interface::{
    borrowck::BodyWithBorrowckFacts,
    middle::{mir, ty::TyCtxt},
    span::def_id::DefId,
};

pub struct CouplingAnalysis<'facts, 'mir: 'facts, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    fact_table: &'facts FactTable<'tcx>,
    body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> CouplingAnalysis<'facts, 'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        fact_table: &'facts FactTable<'tcx>,
        body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> Self {
        CouplingAnalysis {
            tcx,
            def_id,
            fact_table,
            body_with_facts,
        }
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> FixpointEngine<'mir, 'tcx>
    for CouplingAnalysis<'facts, 'mir, 'tcx>
{
    type State = CouplingState<'facts, 'mir, 'tcx>;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        &self.body_with_facts.body
    }

    /// new_bottom must be less than all elements under the join
    /// it consists of an empty vector (no groups),
    /// is that right? or should it be a vector of a single empty group?
    fn new_bottom(&self) -> Self::State {
        // fixme: Mention the rules here
        Self::State::new_bottom(self.body_with_facts, self.fact_table)
    }

    fn new_initial(&self) -> Self::State {
        Self::State::new_empty(self.body_with_facts, self.fact_table)
    }

    /// Model: the counter should never exceed 2
    /// fixme: This might not be true for nested loops, in which case the counter doesn't exceed
    ///     2^|current depth|
    /// at each point. Nested loops with early returns might also complicate this bound, but
    ///     product_{predecessor parent loop heads H} InDegree(H)
    /// seems reasonable. Taking a maximum over all points gets the needs_to_widen bound.
    fn need_to_widen(counter: u32) -> bool {
        assert!(counter <= 3);
        false
    }

    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()> {
        state.apply_statement_effect(location)
    }

    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        state.apply_terminator_effect(location)
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir>
    PointwiseState<'mir, 'tcx, CouplingState<'facts, 'mir, 'tcx>>
{
    // todo: functions which require a full coupling graph trace
    //  - Free PCS trace
    //  - Reborrowing DAG trace
}
