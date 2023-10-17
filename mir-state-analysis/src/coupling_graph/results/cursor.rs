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
    utils::PlaceRepacker, coupling_graph::{engine::CouplingGraph, graph::Graph, CgContext},
};

use super::coupling::CouplingOp;

type Cursor<'a, 'mir, 'tcx> = ResultsCursor<'mir, 'tcx, CouplingGraph<'a, 'tcx>>;

pub struct CgAnalysis<'a, 'mir, 'tcx> {
    cursor: Cursor<'a, 'mir, 'tcx>,
    did_before: bool,
    curr_stmt: Option<Location>,
    end_stmt: Option<Location>,
}

impl<'a, 'mir, 'tcx> CgAnalysis<'a, 'mir, 'tcx> {
    pub(crate) fn new(cursor: Cursor<'a, 'mir, 'tcx>) -> Self {
        Self {
            cursor,
            did_before: false,
            curr_stmt: None,
            end_stmt: None,
        }
    }

    pub fn analysis_for_bb(&mut self, block: BasicBlock) {
        self.cursor.seek_to_block_start(block);
        let end_stmt = self
            .cursor
            .analysis()
            .cgx
            .rp
            .body()
            .terminator_loc(block)
            .successor_within_block();
        self.curr_stmt = Some(Location {
            block,
            statement_index: 0,
        });
        self.end_stmt = Some(end_stmt);
        self.did_before = false;
    }

    fn body(&self) -> &'a Body<'tcx> {
        self.cursor.analysis().cgx.rp.body()
    }
    pub(crate) fn cgx(&mut self) -> &'a CgContext<'a, 'tcx> {
        self.cursor.results().analysis.cgx
    }

    pub fn initial_state(&self) -> &Graph<'tcx> {
        &self.cursor.get().graph
    }
    pub fn initial_coupling(&self) -> &Vec<CouplingOp> {
        &self.cursor.get().couplings
    }
    pub fn before_next(&mut self, exp_loc: Location) -> CgLocation<'tcx> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, exp_loc);
        assert!(location <= self.end_stmt.unwrap());
        assert!(!self.did_before);
        self.did_before = true;
        self.cursor.seek_before_primary_effect(location);
        let state = self.cursor.get();
        CgLocation {
            location,
            state: state.graph.clone(),
            couplings: state.couplings.clone(),
        }
    }
    pub fn next(&mut self, exp_loc: Location) -> CgLocation<'tcx> {
        let location = self.curr_stmt.unwrap();
        assert_eq!(location, exp_loc);
        assert!(location < self.end_stmt.unwrap());
        assert!(self.did_before);
        self.did_before = false;
        self.curr_stmt = Some(location.successor_within_block());

        self.cursor.seek_after_primary_effect(location);
        let state = self.cursor.get();
        CgLocation {
            location,
            state: state.graph.clone(),
            couplings: state.couplings.clone(),
        }
    }
    pub fn terminator(&mut self) -> CgTerminator<'tcx> {
        let location = self.curr_stmt.unwrap();
        assert!(location == self.end_stmt.unwrap());
        assert!(!self.did_before);
        self.curr_stmt = None;
        self.end_stmt = None;

        // TODO: cleanup
        let state = self.cursor.get().clone();
        let block = &self.body()[location.block];
        let succs = block
            .terminator()
            .successors()
            .map(|succ| {
                // Get repacks
                let to = self.cursor.results().entry_set_for_block(succ);
                CgLocation {
                    location: Location {
                        block: succ,
                        statement_index: 0,
                    },
                    state: to.graph.clone(),
                    couplings: state.bridge(&to),
                }
            })
            .collect();
        CgTerminator { succs }
    }

    /// Recommened interface.
    /// Does *not* require that one calls `analysis_for_bb` first
    pub fn get_all_for_bb(&mut self, block: BasicBlock) -> CgBasicBlock<'tcx> {
        self.analysis_for_bb(block);
        let mut statements = Vec::new();
        while self.curr_stmt.unwrap() != self.end_stmt.unwrap() {
            let stmt = self.next(self.curr_stmt.unwrap());
            statements.push(stmt);
        }
        let terminator = self.terminator();
        CgBasicBlock {
            statements,
            terminator,
        }
    }
}

pub struct CgBasicBlock<'tcx> {
    pub statements: Vec<CgLocation<'tcx>>,
    pub terminator: CgTerminator<'tcx>,
}

#[derive(Debug)]
pub struct CgLocation<'tcx> {
    pub location: Location,
    /// Couplings before the statement
    pub couplings: Vec<CouplingOp>,
    /// State after the statement
    pub state: Graph<'tcx>,
}

#[derive(Debug)]
pub struct CgTerminator<'tcx> {
    pub succs: Vec<CgLocation<'tcx>>,
}
