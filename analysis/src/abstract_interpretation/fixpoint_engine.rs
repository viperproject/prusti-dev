// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::AbstractState, analysis_error::AnalysisError::NoStateAfterSuccessor,
    PointwiseState,
};
pub use crate::{domains::*, AnalysisError};
use prusti_rustc_interface::{data_structures::fx::FxHashMap, middle::mir, span::def_id::DefId};
use std::{collections::BTreeSet, iter::FromIterator};

pub type AnalysisResult<T> = std::result::Result<T, AnalysisError>;

/// Trait to be used to define an abstract-interpreation-based static analysis of a MIR body.
pub trait FixpointEngine<'mir, 'tcx: 'mir> {
    type State: AbstractState;

    /// Return the DefId of the MIR body to be analyzed.
    fn def_id(&self) -> DefId;

    /// Return the MIR body to be analyzed.
    fn body(&self) -> &'mir mir::Body<'tcx>;

    /// Creates a new abstract state which corresponds to the bottom element in the lattice
    fn new_bottom(&self) -> Self::State;

    //fn new_top(&self) -> Self::State;

    /// Creates the abstract state at the beginning of the `mir` body.
    /// In particular this should take the arguments into account.
    fn new_initial(&self) -> Self::State;

    /// Determines if the number of times a block was traversed by the analyzer given in `counter`
    /// is large enough to widen the state
    fn need_to_widen(counter: u32) -> bool;

    /// Modify a state according to the statement at `location`.
    ///
    /// The statement can be extracted using
    /// `self.mir[location.block].statements[location.statement_index]`.
    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()>;

    /// Compute the states after a terminator at `location`.
    ///
    /// The statement can be extracted using `self.mir[location.block].terminator()`.
    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>>;

    /// Produces an abstract state for every program point in `mir` by iterating over all statements
    /// in program order until a fixed point is reached (i.e. by abstract interpretation).
    // TODO: add tracing like in initialization.rs?
    fn run_fwd_analysis(&self) -> AnalysisResult<PointwiseState<'mir, 'tcx, Self::State>> {
        let mir = self.body();
        let mut p_state = PointwiseState::new(mir);
        // use https://crates.io/crates/linked_hash_set for set preserving insertion order?
        let mut work_set: BTreeSet<mir::BasicBlock> =
            BTreeSet::from_iter(mir.basic_blocks().indices());

        let mut counters: FxHashMap<mir::BasicBlock, u32> =
            FxHashMap::with_capacity_and_hasher(mir.basic_blocks().len(), Default::default());

        //'block_loop:
        // extract the bb with the minimal index -> hopefully better performance
        // use pop_first when it becomes stable?
        while let Some(&bb) = work_set.iter().next() {
            work_set.remove(&bb);

            let mut state_before_block = if bb == mir::START_BLOCK {
                // entry block
                self.new_initial()
            } else {
                self.new_bottom()
            };

            for &pred_bb in &mir.basic_blocks.predecessors()[bb] {
                if let Some(map) = p_state.lookup_after_block(pred_bb) {
                    // map should contain bb, because we ensure that we have a state for every
                    // successor
                    state_before_block.join(map.get(&bb).unwrap());
                }
                // if no state is present: assume bottom => no effect on join
            }

            // widen if needed
            let counter = counters.entry(bb).or_insert(0);
            *counter += 1;

            if Self::need_to_widen(*counter) {
                let location = mir::Location {
                    block: bb,
                    statement_index: 0,
                };
                state_before_block.widen(p_state.lookup_before(location).unwrap())
            }

            let statements = &mir[bb].statements;
            let mut current_state = state_before_block;
            for statement_index in 0..statements.len() {
                let location = mir::Location {
                    block: bb,
                    statement_index,
                };
                /* Too much performance overhead to check for every statement?
                let prev_state = p_state.lookup_before(location);
                // use .contains when it becomes stable
                if prev_state.into_iter().any(|s| s == &current_state) {
                    // same state, don't need to reiterate
                    continue 'block_loop;
                }
                */
                p_state.set_before(location, current_state.clone());
                // normal statement
                self.apply_statement_effect(&mut current_state, location)?;
            }

            // terminator effect
            let location = mir.terminator_loc(bb);
            /* Too much performance overhead to check for every statement?
            let prev_state = p_state.lookup_before(location);
            if prev_state.into_iter().any(|s| s == &current_state) {
                // same state, don't need to reiterate
                continue 'block_loop;
            }
            */
            p_state.set_before(location, current_state.clone());

            let next_states = self.apply_terminator_effect(&current_state, location)?;

            let mut new_map: FxHashMap<mir::BasicBlock, Self::State> = FxHashMap::default();
            for (next_bb, state) in next_states {
                if let Some(s) = new_map.get_mut(&next_bb) {
                    // join states with same destination for Map
                    s.join(&state);
                } else {
                    new_map.insert(next_bb, state);
                }
            }

            let terminator = mir[bb].terminator();
            for next_bb in terminator.successors() {
                if !new_map.contains_key(&next_bb) {
                    return Err(NoStateAfterSuccessor(bb, next_bb));
                }
            }
            debug_assert_eq!(
                terminator.successors().collect::<BTreeSet<_>>(),
                new_map.keys().copied().collect::<BTreeSet<_>>(),
            );
            let map_after_block = p_state.lookup_mut_after_block(bb);
            for next_bb in terminator.successors() {
                if let Some(s) = new_map.remove(&next_bb) {
                    let prev_state = map_after_block.insert(next_bb, s);
                    let new_state_ref = map_after_block.get(&next_bb);
                    // TODO: use .contains when it becomes stable?
                    if !prev_state.iter().any(|ps| ps == new_state_ref.unwrap()) {
                        // input state has changed => add next_bb to worklist
                        work_set.insert(next_bb);
                    }
                }
            }
        }
        AnalysisResult::Ok(p_state)
    }
}
