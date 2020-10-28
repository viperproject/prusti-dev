// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::ty::TyCtxt;
use rustc_middle::mir;
pub use crate::PointwiseState;
pub use crate::AnalysisError;
pub use crate::abstract_domains::*;
use crate::AbstractState;
use std::collections::{HashMap, BTreeSet};
use std::iter::FromIterator;
use crate::analysis_error::AnalysisError::SuccessorWithoutState;

type Result<T> = std::result::Result<T, AnalysisError>;

pub struct Analyzer<'tcx> {         // S: AbstractState<'tcx>
    tcx: TyCtxt<'tcx>,
    //p_state: PointwiseState<S>,
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Analyzer {
            tcx,
            //p_state: PointwiseState::new(),
        }
    }


    pub fn run_fwd_analysis<S>(&self, mir:  &mir::Body<'tcx>,) -> Result<PointwiseState<S>>
        where S: AbstractState + Clone + Eq
    {
        let mut p_state = PointwiseState::new();
        //use https://crates.io/crates/linked_hash_set for set preserving insertion order?
        let mut work_set: BTreeSet<mir::BasicBlock> = BTreeSet::from_iter(mir.basic_blocks().indices());

        let mut counters: HashMap<mir::BasicBlock, u32> = HashMap::with_capacity(mir.basic_blocks().len());

        'block_loop:    // extract the bb with the minimal index -> hopefully better performance
        while let Some(&bb) = work_set.iter().next() {      //use pop_first when it becomes stable?
            work_set.remove(&bb);

            let mut state_before_block;
            if bb == mir::START_BLOCK {
                // entry block
                state_before_block = S::new_initial(
                    mir.args_iter().map(|local| mir.local_decls.get(local).unwrap())    //TODO: handle unwrap error?
                    .collect::<Vec<&mir::LocalDecl>>());
            }
            else {
                state_before_block = S::new_bottom();
            }

            for pred_bb in &mir.predecessors()[bb] {
                if let Some(map) = p_state.lookup_after_block(pred_bb) {
                    state_before_block.join(map.get(&bb).unwrap());      //TODO: handle unwrap error?
                }
            }

                // widen if needed
                let counter = counters.entry(bb).or_insert(0);
                *counter += 1;

            if S::need_to_widen(counter) {
                let location = mir::Location {
                    block: bb,
                    statement_index: 0,
                };
                state_before_block.widen(p_state.lookup_before(&location).unwrap())
            }

            let mir::BasicBlockData { ref statements, .. } = mir[bb];
            let mut current_state = state_before_block;
            for statement_index in 0..statements.len() {
                let location = mir::Location {
                    block: bb,
                    statement_index,
                };
                /* Too much performance overhead to check for every statement?
                let prev_state = p_state.lookup_before(&location);
                if prev_state.into_iter().any(|s| s == &current_state) {      //use .contains when it becomes stable
                    // same state, don't need to reiterate
                    continue 'block_loop;
                }*/
                p_state.set_before(&location, current_state.clone());
                // normal statement
                let stmt = &statements[statement_index];
                let res = current_state.apply_statement_effect(&location, stmt);
                if res.is_err() {
                    return Err(res.unwrap_err());
                }
            }

            // terminator effect
            let location = mir.terminator_loc(bb);
            /* Too much performance overhead to check for every statement?
            let prev_state = p_state.lookup_before(&location);
            if prev_state.into_iter().any(|s| s == &current_state) {
                // same state, don't need to reiterate
                continue 'block_loop;
            }*/
            p_state.set_before(&location, current_state.clone());

            let terminator = mir[bb].terminator();
            let term_res = current_state.apply_terminator_effect(&location, terminator);

            match term_res {
                Err(e) => {return Err(e);}
                Ok(next_states) => {
                    let mut new_map: HashMap<mir::BasicBlock, S> = HashMap::new();
                    for (next_bb, state) in next_states {
                        if let Some(s) = new_map.get_mut(&next_bb) {
                            s.join(&state);      // join states with same destination for Map
                        }
                        else {
                            new_map.insert(next_bb, state);
                        }
                    }

                    let map_after_block = p_state.lookup_mut_after_block(&bb);
                    for next_bb in terminator.successors() {
                        if let Some(s) = new_map.remove(next_bb) {
                            let prev_state = map_after_block.insert(*next_bb, s);
                            let new_state_ref = map_after_block.get(&next_bb);
                            if !prev_state.iter().any(|ps| ps == new_state_ref.unwrap()) {       //use .contains when it becomes stable
                                // input state has changed => add next_bb to worklist
                                work_set.insert(*next_bb);
                            }
                        }
                        else {
                            return Err(SuccessorWithoutState(location, *next_bb));
                        }
                    }
                }
            }
        }

        Result::Ok(p_state)
    }

}
