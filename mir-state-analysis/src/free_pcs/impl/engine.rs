// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    dataflow::{Analysis, AnalysisDomain},
    index::IndexVec,
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Location, Promoted,
            Statement, Terminator, TerminatorEdges,
        },
        ty::TyCtxt,
    },
};

use crate::{
    utils::PlaceRepacker,
};

use super::{triple::{Stage, TripleWalker}, FreePlaceCapabilitySummary};

pub struct FpcsEngine<'a, 'tcx>(pub PlaceRepacker<'a, 'tcx>);

impl<'a, 'tcx> AnalysisDomain<'tcx> for FpcsEngine<'a, 'tcx> {
    type Domain = FreePlaceCapabilitySummary<'a, 'tcx>;
    const NAME: &'static str = "free_pcs";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        FreePlaceCapabilitySummary::new(self.0)
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        state.initialize_as_start_block();
    }
}

impl<'a, 'tcx> Analysis<'tcx> for FpcsEngine<'a, 'tcx> {
    #[tracing::instrument(
        name = "FpcsEngine::apply_before_statement_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        TripleWalker::prepare(&mut state.after, self.0, Stage::Before).visit_statement(statement, location);
        state.before_start = state.after.clone();
        TripleWalker::apply(&mut state.after, self.0, Stage::Before).visit_statement(statement, location);
        state.before_after = state.after.clone();
    }
    #[tracing::instrument(
        name = "FpcsEngine::apply_statement_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        TripleWalker::prepare(&mut state.after, self.0, Stage::Main).visit_statement(statement, location);
        state.start = state.after.clone();
        TripleWalker::apply(&mut state.after, self.0, Stage::Main).visit_statement(statement, location);
    }

    #[tracing::instrument(
        name = "FpcsEngine::apply_before_terminator_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        TripleWalker::prepare(&mut state.after, self.0, Stage::Before).visit_terminator(terminator, location);
        state.before_start = state.after.clone();
        TripleWalker::apply(&mut state.after, self.0, Stage::Before).visit_terminator(terminator, location);
        state.before_after = state.after.clone();
    }
    #[tracing::instrument(
        name = "FpcsEngine::apply_terminator_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        TripleWalker::prepare(&mut state.after, self.0, Stage::Main).visit_terminator(terminator, location);
        state.start = state.after.clone();
        TripleWalker::apply(&mut state.after, self.0, Stage::Main).visit_terminator(terminator, location);
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
