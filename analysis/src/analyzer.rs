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
use std::collections::{VecDeque, HashMap};
use std::iter::FromIterator;

type Result<T> = std::result::Result<T, AnalysisError>;

pub struct Analyzer<'tcx> {         // S: AbstractState<'tcx>
    tcx: TyCtxt<'tcx>,
    //p_state: PointwiseState<'tcx, S>,
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Analyzer {
            tcx,
            //p_state: PointwiseState::new(tcx),
        }
    }

    /*fn initialize_states(&mut self, mir:  &mir::Body<'tcx>,) {
        for bb in mir.basic_blocks().indices() {
            p_state.before_block.insert(bb, AssignmentSet::new());
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            for statement_index in 0..statements.len() + 1 {
                let location = mir::Location {
                    block: bb,
                    statement_index: statement_index,
                };
                self.result
                    .after_statement
                    .insert(location, AssignmentSet::new());
            }
        }
    }*/

    pub fn run_fwd_analysis<S>(&mut self, tcx: TyCtxt<'tcx>, mir:  &mir::Body<'tcx>,) -> Result<PointwiseState<'tcx, S>>
        where S: AbstractState<'tcx> + Clone + Eq
    {
        let mut p_state = PointwiseState::new(tcx);
        //TODO: use https://crates.io/crates/linked_hash_set for set preserving insertion order? Or Btreeset -> extract minimal element
        let mut work_list: VecDeque<mir::BasicBlock> = VecDeque::from_iter(mir.basic_blocks().indices()); //TODO: guaranteed order? Only take first?

        //TODO: maybe initialize all after_block first to bottom?

        let mut counters: HashMap<mir::BasicBlock, u32> = HashMap::with_capacity(work_list.len());

        'block_loop:
        while let Some(bb) = work_list.pop_front() {
            let mut state_before_block;
            if mir.predecessors()[bb].is_empty() {
                //TODO: extract arguments from localDecl?
                //state_before_block = S::new_initial(mir.local_decls.get(1..=mir.arg_count));
                state_before_block = S::new_bottom();
            }
            else {
                state_before_block = S::new_bottom();
                for pred_bb in &mir.predecessors()[bb] {
                    if let Some(map) = p_state.lookup_after_block(pred_bb) {
                        state_before_block.join(map.get(&bb).unwrap());      //TODO: handle error?
                    }
                }

                // widen if needed
                let counter = counters.entry(bb).or_insert(0);
                *counter += 1;

                if *counter > S::widening_threshold() {
                    let location = mir::Location {
                        block: bb,
                        statement_index: 0,
                    };
                    state_before_block.widen(p_state.lookup_before(&location).unwrap())
                }
            }

            let mir::BasicBlockData { ref statements, .. } = mir[bb];
            let mut current_state = state_before_block;
            for statement_index in 0..statements.len() {
                let location = mir::Location {
                    block: bb,
                    statement_index,
                };
                let prev_state = p_state.lookup_before(&location);
                if prev_state.is_some() && prev_state.unwrap() == &current_state {
                    // same state, don't need to reiterate
                    continue 'block_loop;
                }
                p_state.set_before(&location, current_state.clone());
                // normal statement
                let stmt = &statements[statement_index];
                current_state.apply_statement_effect(&location, stmt);
            }

            // terminator effect
            let location = mir::Location {
                block: bb,
                statement_index: statements.len(),
            };
            let prev_state = p_state.lookup_before(&location);
            if prev_state.is_some() && prev_state.unwrap() == &current_state {
                // same state, don't need to reiterate
                continue 'block_loop;
            }
            p_state.set_before(&location, current_state.clone());

            let terminator = mir[bb].terminator();
            let next_states = current_state.apply_terminator_effect(&location, terminator);
            let map_after_block = p_state.lookup_mut_after_block(&bb);
            for (next_bb, state) in next_states {
                let prev_state = map_after_block.insert(next_bb, *state);
                let new_state_ref = map_after_block.get(&next_bb);
                if prev_state.is_none() || &prev_state.unwrap() != new_state_ref.unwrap() {
                    // input state has changed => add next_bb to worklist again
                    work_list.push_back(next_bb);
                }
            }
        }

        return Result::Ok(p_state);
    }

    /*pub fn liveness_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> Result<PointwiseState<LivenessState>> {
        unimplemented!();
    }

    pub fn definitely_initialized_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> Result<PointwiseState<DefinitelyInitializedState>> {
        unimplemented!();
    }

    pub fn pcs_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> Result<PointwiseState<PCSState>> {
        unimplemented!();
    }*/
}
