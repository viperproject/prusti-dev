// © 2019, ETH Zurich
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

use prusti_common::Stopwatch;
use super::common::{self, WorkItem};
use crate::environment::place_set::PlaceSet;
use csv::{ReaderBuilder, WriterBuilder};
use rustc_middle::ty::TyCtxt;
use rustc_middle::mir;
use rustc_hir as hir;
use rustc_index::vec::Idx;
use std::path::Path;
use log::trace;
use serde::{Serialize, Deserialize};
use analysis::{Analyzer, AbstractState};
use analysis::abstract_domains::DefinitelyInitializedState;

/// The result of the definitely initialized analysis.
pub type DefinitelyInitializedAnalysisResult<'tcx> = common::AnalysisResult<PlaceSet<'tcx>>;

pub fn compute_definitely_initialized<'a, 'tcx: 'a>(
    body: &'a mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> DefinitelyInitializedAnalysisResult<'tcx> {
    let stopwatch = Stopwatch::start_debug("prusti-client", "initialization analysis");
    let analyzer = Analyzer::new(tcx);
    let pointwise_state = analyzer.run_fwd_analysis::<DefinitelyInitializedState>(body)
        .map_err(|e| panic!("Error while analyzing function at {:?}: {}", body.span, e.to_pretty_str(body)))
        .unwrap();

    // Convert the pointwise_state to analysis_result.
    let mut analysis_result = common::AnalysisResult::new();
    for (bb, bb_data) in body.basic_blocks().iter_enumerated() {
        let num_statements = bb_data.statements.len();
        let mut location = bb.start_location();
        analysis_result.before_block.insert(
            bb,
            pointwise_state.lookup_before(location).unwrap().get_def_init_places().clone().into(),
        );
        while location.statement_index < num_statements {
            // `location` identifies a statement
            let state = pointwise_state.lookup_after(location).unwrap();
            analysis_result.after_statement.insert(
                location,
                state.get_def_init_places().clone().into(),
            );
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
        let state_after_block = opt_state_after_block.unwrap_or_else(
            || DefinitelyInitializedState::new_bottom(body, tcx)
        );
        analysis_result.after_statement.insert(
            location,
            state_after_block.get_def_init_places().clone().into()
        );
    }
    stopwatch.finish();
    analysis_result
}
