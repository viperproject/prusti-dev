// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module provides the definitely initialized analysis for MIR.
//!
//!
//! Definitely initialized:
//!
//! The working set `S` is the set of paths whose leaves are definitely
//! initialized. For example, if we have `x.f` in `S`, then we know that
//! `x.f.g` and `x.f.h` are definitely initialized. The invariant of
//! this set is that we never have a node and any of its descendents in
//! the set at the same time. For example, having `x.f` and `x.f.g` in
//! `S` at the same time is illegal.

use crate::environment::place_set::PlaceSet;
use analysis::{domains::DefinitelyInitializedAnalysis};
use csv::{ReaderBuilder, WriterBuilder};
use log::trace;
use prusti_common::Stopwatch;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_index::vec::Idx;
use rustc_middle::{mir, ty::TyCtxt};
use serde::{Deserialize, Serialize};
use std::{collections::HashMap, path::Path};
use analysis::abstract_interpretation::{FixpointEngine, AbstractState};

pub struct AnalysisResult<T> {
    /// The state before the basic block.
    pub before_block: FxHashMap<mir::BasicBlock, T>,
    /// The state after the statement.
    pub after_statement: FxHashMap<mir::Location, T>,
}

impl<T> AnalysisResult<T> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {
            before_block: FxHashMap::default(),
            after_statement: FxHashMap::default(),
        }
    }
    /// Get the initialization set before the first statement of the
    /// basic block.
    pub fn get_before_block(&self, bb: mir::BasicBlock) -> &T {
        self.before_block
            .get(&bb)
            .unwrap_or_else(|| panic!("Missing initialization info for block {:?}", bb))
    }
    /// Get the initialization set after the statement.
    /// If `location.statement_index` is equal to the number of statements,
    /// returns the initialization set after the terminator.
    pub fn get_after_statement(&self, location: mir::Location) -> &T {
        self.after_statement
            .get(&location)
            .unwrap_or_else(|| panic!("Missing initialization info for location {:?}", location))
    }
}

/// The result of the definitely initialized analysis.
pub type DefinitelyInitializedAnalysisResult<'tcx> = AnalysisResult<PlaceSet<'tcx>>;

pub fn compute_definitely_initialized<'a, 'tcx: 'a>(
    def_id: DefId,
    body: &'a mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> DefinitelyInitializedAnalysisResult<'tcx> {
    let stopwatch = Stopwatch::start_debug("prusti-client", "initialization analysis");
    let analysis = DefinitelyInitializedAnalysis::new(tcx, def_id, body);
    let pointwise_state = analysis
        .run_fwd_analysis()
        .map_err(|e| {
            panic!(
                "Error while analyzing function at {:?}: {}",
                body.span,
                e.to_pretty_str(body)
            )
        })
        .unwrap();

    // Convert the pointwise_state to analysis_result.
    // TODO: Replace AnalysisResult with PointwiseState, to avoid this conversion.
    let mut analysis_result = AnalysisResult::new();
    for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
        let num_statements = bb_data.statements.len();
        let mut location = bb.start_location();
        analysis_result.before_block.insert(
            bb,
            pointwise_state
                .lookup_before(location)
                .unwrap()
                .get_def_init_places()
                .clone()
                .into(),
        );
        while location.statement_index < num_statements {
            // `location` identifies a statement
            let state = pointwise_state.lookup_after(location).unwrap();
            analysis_result
                .after_statement
                .insert(location, state.get_def_init_places().clone().into());
            location = location.successor_within_block();
        }
        // `location` identifies a terminator
        let mut states_after_block = pointwise_state.lookup_after_block(bb).unwrap().values();
        let mut opt_state_after_block = states_after_block.next().cloned();
        if let Some(curr_state) = opt_state_after_block.as_mut() {
            for state in states_after_block {
                curr_state.join(state);
            }
        }
        let state_after_block = opt_state_after_block.unwrap_or_else(|| analysis.new_bottom());
        analysis_result.after_statement.insert(
            location,
            state_after_block.get_def_init_places().clone().into(),
        );
    }
    stopwatch.finish();
    analysis_result
}
