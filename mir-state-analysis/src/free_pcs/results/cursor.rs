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

pub struct FreePcsAnalysis<'mir, 'tcx> {
    cursor: Cursor<'mir, 'tcx>,
    curr_stmt: Option<Location>,
    end_stmt: Option<Location>,
}

impl<'mir, 'tcx> FreePcsAnalysis<'mir, 'tcx> {
    pub(crate) fn new(cursor: Cursor<'mir, 'tcx>) -> Self {
        Self {
            cursor,
            curr_stmt: None,
            end_stmt: None,
        }
    }

    pub fn analysis_for_bb(&mut self, block: BasicBlock) {
        self.cursor.seek_to_block_start(block);
        let end_stmt = self
            .cursor
            .analysis()
            .0
            .body()
            .terminator_loc(block)
            .successor_within_block();
        self.curr_stmt = Some(Location {
            block,
            statement_index: 0,
        });
        self.end_stmt = Some(end_stmt);
    }

    fn body(&self) -> &'mir Body<'tcx> {
        self.cursor.analysis().0.body()
    }
    pub(crate) fn repacker(&mut self) -> PlaceRepacker<'mir, 'tcx> {
        self.cursor.results().analysis.0
    }

    pub fn initial_state(&self) -> &CapabilitySummary<'tcx> {
        &self.cursor.get().summary
    }
    pub fn next(&mut self, exp_loc: Location) -> FreePcsLocation<'tcx> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, exp_loc);
        assert!(location < self.end_stmt.unwrap());
        self.curr_stmt = Some(location.successor_within_block());

        self.cursor.seek_before_primary_effect(location);
        let repacks_start = self.cursor.get().repackings.clone();
        self.cursor.seek_after_primary_effect(location);
        let state = self.cursor.get();
        FreePcsLocation {
            location,
            state: state.summary.clone(),
            repacks_start,
            repacks_middle: state.repackings.clone(),
        }
    }
    pub fn terminator(&mut self) -> FreePcsTerminator<'tcx> {
        let location = self.curr_stmt.unwrap();
        assert!(location == self.end_stmt.unwrap());
        self.curr_stmt = None;
        self.end_stmt = None;

        // TODO: cleanup
        let rp: PlaceRepacker = self.repacker();
        let state = self.cursor.get().clone();
        let block = &self.body()[location.block];
        let succs = block
            .terminator()
            .successors()
            .map(|succ| {
                // Get repacks
                let to = self.cursor.results().entry_set_for_block(succ);
                FreePcsLocation {
                    location: Location {
                        block: succ,
                        statement_index: 0,
                    },
                    state: to.summary.clone(),
                    repacks_start: state.summary.bridge(&to.summary, rp),
                    repacks_middle: Vec::new(),
                }
            })
            .collect();
        FreePcsTerminator { succs }
    }

    /// Recommened interface.
    /// Does *not* require that one calls `analysis_for_bb` first
    pub fn get_all_for_bb(&mut self, block: BasicBlock) -> FreePcsBasicBlock<'tcx> {
        self.analysis_for_bb(block);
        let mut statements = Vec::new();
        while self.curr_stmt.unwrap() != self.end_stmt.unwrap() {
            let stmt = self.next(self.curr_stmt.unwrap());
            statements.push(stmt);
        }
        let terminator = self.terminator();
        FreePcsBasicBlock {
            statements,
            terminator,
        }
    }
}

pub struct FreePcsBasicBlock<'tcx> {
    pub statements: Vec<FreePcsLocation<'tcx>>,
    pub terminator: FreePcsTerminator<'tcx>,
}

#[derive(Debug)]
pub struct FreePcsLocation<'tcx> {
    pub location: Location,
    /// Repacks before the statement
    pub repacks_start: Vec<RepackOp<'tcx>>,
    /// Repacks in the middle of the statement
    pub repacks_middle: Vec<RepackOp<'tcx>>,
    /// State after the statement
    pub state: CapabilitySummary<'tcx>,
}

#[derive(Debug)]
pub struct FreePcsTerminator<'tcx> {
    pub succs: Vec<FreePcsLocation<'tcx>>,
}
