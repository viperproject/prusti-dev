// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::AnalysisResult,
    domains::{DefinitelyAccessibleAnalysis, DefinitelyAccessibleState, FramingState},
    mir_utils::{get_blocked_place, remove_place_from_set},
    PointwiseState,
};
use prusti_rustc_interface::{
    borrowck::BodyWithBorrowckFacts,
    middle::{
        mir,
        mir::visit::{NonMutatingUseContext, PlaceContext, Visitor},
        ty::TyCtxt,
    },
    span::def_id::DefId,
};

pub struct FramingAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'mir, 'tcx: 'mir> FramingAnalysis<'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> Self {
        FramingAnalysis {
            tcx,
            def_id,
            body_with_facts,
        }
    }

    pub fn run_analysis(&self) -> AnalysisResult<PointwiseState<'mir, 'tcx, FramingState<'tcx>>> {
        let acc_analysis =
            DefinitelyAccessibleAnalysis::new(self.tcx, self.def_id, self.body_with_facts);
        let accessibility = acc_analysis.run_analysis()?;
        let body = &self.body_with_facts.body;
        let mut analysis_state = PointwiseState::default(body);

        // Set state_after_block
        for (block, block_data) in body.basic_blocks().iter_enumerated() {
            // Initialize the state before each statement and terminator
            for statement_index in 0..=block_data.statements.len() {
                let location = mir::Location {
                    block,
                    statement_index,
                };
                let acc_before = accessibility.lookup_before(location).unwrap_or_else(|| {
                    panic!("No 'accessibility' state before location {:?}", location)
                });
                let mut compute_framing = ComputeFramingState::initial(body, self.tcx, acc_before);
                if let Some(stmt) = body.stmt_at(location).left() {
                    compute_framing.visit_statement(stmt, location);
                }
                if let Some(term) = body.stmt_at(location).right() {
                    compute_framing.visit_terminator(term, location);
                }
                let state = compute_framing.state;
                state.check_invariant(acc_before, location);
                analysis_state.set_before(location, state);
            }

            // Leave empty the state after terminators
        }

        Ok(analysis_state)
    }
}

struct ComputeFramingState<'mir, 'tcx: 'mir> {
    body: &'mir mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    state: FramingState<'tcx>,
}

impl<'mir, 'tcx: 'mir> ComputeFramingState<'mir, 'tcx> {
    pub fn initial(
        body: &'mir mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        acc: &DefinitelyAccessibleState<'tcx>,
    ) -> Self {
        let state = FramingState {
            framed_accessible: acc.get_definitely_accessible().clone(),
            framed_owned: acc.get_definitely_owned().clone(),
        };
        ComputeFramingState { body, tcx, state }
    }
}

impl<'mir, 'tcx: 'mir> Visitor<'tcx> for ComputeFramingState<'mir, 'tcx> {
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: PlaceContext,
        _location: mir::Location,
    ) {
        let place = (*place).into();
        match context {
            PlaceContext::NonMutatingUse(NonMutatingUseContext::UniqueBorrow) => todo!(),
            PlaceContext::MutatingUse(_)
            | PlaceContext::NonMutatingUse(NonMutatingUseContext::Move) => {
                // No permission can be framed
                let blocked_place = get_blocked_place(self.tcx, place);
                remove_place_from_set(
                    self.body,
                    self.tcx,
                    blocked_place,
                    &mut self.state.framed_owned,
                );
                remove_place_from_set(
                    self.body,
                    self.tcx,
                    blocked_place,
                    &mut self.state.framed_accessible,
                );
            }
            PlaceContext::NonMutatingUse(_) => {
                // Read permission can be framed
                let frozen_place = get_blocked_place(self.tcx, place);
                remove_place_from_set(
                    self.body,
                    self.tcx,
                    frozen_place,
                    &mut self.state.framed_owned,
                );
            }
            PlaceContext::NonUse(_) => {
                // Any permission can be framed
            }
        }
    }
}
