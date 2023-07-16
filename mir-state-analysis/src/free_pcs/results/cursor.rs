// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    dataflow::ResultsCursor,
    middle::mir::{BasicBlock, Body, Location},
};

use crate::{
    free_pcs::{
        engine::FreePlaceCapabilitySummary, join_semi_lattice::RepackingJoinSemiLattice,
        CapabilitySummary, RepackOp,
    },
    utils::PlaceRepacker,
};

type Cursor<'mir, 'tcx> = ResultsCursor<'mir, 'tcx, FreePlaceCapabilitySummary<'mir, 'tcx>>;

pub struct FreePcsAnalysis<'mir, 'tcx>(pub(crate) Cursor<'mir, 'tcx>);

impl<'mir, 'tcx> FreePcsAnalysis<'mir, 'tcx> {
    pub fn analysis_for_bb(&mut self, block: BasicBlock) -> FreePcsCursor<'_, 'mir, 'tcx> {
        self.0.seek_to_block_start(block);
        let end_stmt = self
            .0
            .analysis()
            .0
            .body()
            .terminator_loc(block)
            .successor_within_block();
        FreePcsCursor {
            analysis: self,
            curr_stmt: Location {
                block,
                statement_index: 0,
            },
            end_stmt,
        }
    }

    pub(crate) fn body(&self) -> &'mir Body<'tcx> {
        self.0.analysis().0.body()
    }
    pub(crate) fn repacker(&mut self) -> PlaceRepacker<'mir, 'tcx> {
        self.0.results().analysis.0
    }
}

pub struct FreePcsCursor<'a, 'mir, 'tcx> {
    analysis: &'a mut FreePcsAnalysis<'mir, 'tcx>,
    curr_stmt: Location,
    end_stmt: Location,
}

impl<'a, 'mir, 'tcx> FreePcsCursor<'a, 'mir, 'tcx> {
    pub fn initial_state(&self) -> &CapabilitySummary<'tcx> {
        &self.analysis.0.get().summary
    }
    pub fn next<'b>(
        &'b mut self,
    ) -> Result<FreePcsLocation<'b, 'tcx>, FreePcsTerminator<'b, 'tcx>> {
        let location = self.curr_stmt;
        assert!(location <= self.end_stmt);
        self.curr_stmt = location.successor_within_block();

        if location == self.end_stmt {
            // TODO: cleanup
            let cursor = &mut self.analysis.0;
            let state = cursor.get();
            let rp = self.analysis.repacker();
            let block = &self.analysis.body()[location.block];
            let succs = block
                .terminator()
                .successors()
                .map(|succ| {
                    // Get repacks
                    let to = cursor.results().entry_set_for_block(succ);
                    FreePcsLocation {
                        location: Location {
                            block: succ,
                            statement_index: 0,
                        },
                        state: &to.summary,
                        repacks: state.summary.bridge(&to.summary, rp),
                    }
                })
                .collect();
            Err(FreePcsTerminator { succs })
        } else {
            self.analysis.0.seek_after_primary_effect(location);
            let state = self.analysis.0.get();
            Ok(FreePcsLocation {
                location,
                state: &state.summary,
                repacks: state.repackings.clone(),
            })
        }
    }
}

#[derive(Debug)]
pub struct FreePcsLocation<'a, 'tcx> {
    pub location: Location,
    /// Repacks before the statement
    pub repacks: Vec<RepackOp<'tcx>>,
    /// State after the statement
    pub state: &'a CapabilitySummary<'tcx>,
}

#[derive(Debug)]
pub struct FreePcsTerminator<'a, 'tcx> {
    pub succs: Vec<FreePcsLocation<'a, 'tcx>>,
}
