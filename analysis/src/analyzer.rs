// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub use crate::{abstract_domains::*, AnalysisError, PointwiseState};
use crate::{analysis_error::AnalysisError::SuccessorWithoutState, AbstractState};
use rustc_middle::{mir, ty::TyCtxt};
use std::{
    collections::{BTreeSet, HashMap},
    iter::FromIterator,
};

type Result<T> = std::result::Result<T, AnalysisError>;

pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx: 'a> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Analyzer { tcx }
    }

    /// Produces an abstract state for every program point in `mir` by iterating over all statements
    /// in program order until a fixed point is reached (i.e. by abstract interpretation).
    // TODO: add tracing like in initialization.rs?
    pub fn run_fwd_analysis<S: AbstractState<'a, 'tcx>>(
        &self,
        mir: &'a mir::Body<'tcx>,
    ) -> Result<PointwiseState<'a, 'tcx, S>> {
        let mut p_state = PointwiseState::new(mir, self.tcx);
        // use https://crates.io/crates/linked_hash_set for set preserving insertion order?
        let mut work_set: BTreeSet<mir::BasicBlock> =
            BTreeSet::from_iter(mir.basic_blocks().indices());

        let mut counters: HashMap<mir::BasicBlock, u32> =
            HashMap::with_capacity(mir.basic_blocks().len());

        //'block_loop:
        // extract the bb with the minimal index -> hopefully better performance
        // use pop_first when it becomes stable?
        while let Some(&bb) = work_set.iter().next() {
            work_set.remove(&bb);

            let mut state_before_block;
            if bb == mir::START_BLOCK {
                // entry block
                state_before_block = S::new_initial(mir, self.tcx);
            } else {
                state_before_block = S::new_bottom(mir, self.tcx);
            }

            for &pred_bb in &mir.predecessors()[bb] {
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

            if S::need_to_widen(counter) {
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
                current_state.apply_statement_effect(location)?;
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

            let next_states = current_state.apply_terminator_effect(location)?;

            let mut new_map: HashMap<mir::BasicBlock, S> = HashMap::new();
            for (next_bb, state) in next_states {
                if let Some(s) = new_map.get_mut(&next_bb) {
                    // join states with same destination for Map
                    s.join(&state);
                } else {
                    new_map.insert(next_bb, state);
                }
            }

            let terminator = mir[bb].terminator();
            for &next_bb in terminator.successors() {
                if !new_map.contains_key(&next_bb) {
                    return Err(SuccessorWithoutState(location, next_bb));
                }
            }
            debug_assert_eq!(
                terminator.successors().collect::<BTreeSet<_>>(),
                new_map.keys().collect::<BTreeSet<_>>(),
            );
            let map_after_block = p_state.lookup_mut_after_block(bb);
            for &next_bb in terminator.successors() {
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
        Result::Ok(p_state)
    }
}
