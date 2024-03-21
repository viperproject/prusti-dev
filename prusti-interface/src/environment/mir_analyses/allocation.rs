// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module provides the definitely allocated analysis for MIR.
//!
//!
//! Definitely allocated:
//!
//! A local `x` is definitely allocated if either there is no
//! `StorageLive(x)`/`StorageDead(x)` in MIR or on all paths leading to the
//! current statement `x` was allocated with `StorageLive(x)` and was not
//! deallocated with `StorageDead(x)`.

use super::initialization::AnalysisResult;
use crate::environment::mir_sets::LocalSet;
use analysis::{
    abstract_interpretation::{AbstractState, FixpointEngine},
    domains::DefinitelyAllocatedAnalysis,
};
use prusti_utils::Stopwatch;
use prusti_rustc_interface::{hir::def_id::DefId, middle::mir};

/// The result of the definitely allocated analysis.
pub type DefinitelyAllocatedAnalysisResult = AnalysisResult<LocalSet>;

pub fn compute_definitely_allocated<'a, 'tcx: 'a>(
    def_id: DefId,
    body: &'a mir::Body<'tcx>,
) -> DefinitelyAllocatedAnalysisResult {
    let stopwatch = Stopwatch::start_debug("prusti-client", "allocation analysis");
    let analysis = DefinitelyAllocatedAnalysis::new(def_id, body);
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
    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        let num_statements = bb_data.statements.len();
        let mut location = bb.start_location();
        analysis_result.before_block.insert(
            bb,
            pointwise_state
                .lookup_before(location)
                .unwrap()
                .get_def_allocated_locals()
                .clone()
                .into(),
        );
        while location.statement_index < num_statements {
            // `location` identifies a statement
            let state = pointwise_state.lookup_after(location).unwrap();
            analysis_result
                .after_statement
                .insert(location, state.get_def_allocated_locals().clone().into());
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
            state_after_block.get_def_allocated_locals().clone().into(),
        );
    }
    stopwatch.finish();
    analysis_result
}
