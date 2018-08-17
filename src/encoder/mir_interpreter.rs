// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::mir;
use std::collections::HashMap;
use std::marker::Sized;
use std::iter::FromIterator;
use std::fmt::Debug;

/// Backward interpreter for a loop-less MIR
pub trait BackwardMirInterpreter<'tcx> {
    type State : Sized;
    fn apply_terminator(&self, terminator: &mir::Terminator<'tcx>, states: HashMap<mir::BasicBlock, &Self::State>) -> Self::State;
    fn apply_statement(&self, stmt: &mir::Statement<'tcx>, state: &mut Self::State);
}

/// Interpret a loop-less MIR starting from the end and return the **initial** state.
/// The result is None if the CFG contains a loop.
pub fn run_backward_interpretation<'tcx, S: Debug, I: BackwardMirInterpreter<'tcx, State = S>>(mir: &mir::Mir<'tcx>, interpreter: &I) -> Option<S> {
    let basic_blocks = mir.basic_blocks();
    let mut heads: HashMap<mir::BasicBlock, S> = HashMap::new();
    let mut predecessors: HashMap<mir::BasicBlock, Vec<mir::BasicBlock>> = HashMap::new();

    // Compute the predecessors of each MIR block
    for bb in basic_blocks.indices() {
        predecessors.insert(bb, vec![]);
    }
    for (bb, bb_data) in basic_blocks.iter_enumerated() {
        if let Some(ref term) = bb_data.terminator {
            for succ_bb in term.successors() {
                let preds_of_succ = predecessors.get_mut(succ_bb).unwrap();
                preds_of_succ.push(bb);
            }
        }
    }

    // Find the final basic blocks
    let mut pending_blocks: Vec<mir::BasicBlock> = basic_blocks.iter_enumerated().filter(
        |(_, bb_data)| match bb_data.terminator {
            Some(ref term) => term.successors().next().is_none(),
            _ => false
        }
    ).map(|(bb, _)| bb).collect();

    // Interpret all the blocks in `pending_blocks`
    while !pending_blocks.is_empty() {
        let curr_bb = pending_blocks.pop().unwrap();
        let bb_data = &basic_blocks[curr_bb];

        // Apply the terminator
        let terminator = bb_data.terminator.as_ref().unwrap();
        let states = HashMap::from_iter(
            terminator.successors().map(|bb| (*bb, &heads[bb]))
        );
        trace!("States before: {:?}", states);
        trace!("Apply terminator {:?}", terminator);
        let mut curr_state = interpreter.apply_terminator(
            terminator,
            states
        );
        trace!("State after: {:?}", curr_state);

        // Apply each statement, from the last
        for stmt in bb_data.statements.iter().rev() {
            trace!("State before: {:?}", curr_state);
            trace!("Apply statement {:?}", stmt);
            interpreter.apply_statement(stmt, &mut curr_state);
            trace!("State after: {:?}", curr_state);
        }

        // Store the state at the beginning of block `curr_bb`
        heads.insert(curr_bb, curr_state);

        // Put the preceding basic blocks
        for pred_bb in &predecessors[&curr_bb] {
            if let Some(ref term) = basic_blocks[*pred_bb].terminator {
                if term.successors().all(|succ_bb| heads.contains_key(succ_bb)) {
                    pending_blocks.push(*pred_bb);
                }
            }
        }
    }

    let result = heads.remove(&basic_blocks.indices().next().unwrap());

    if result.is_none() {
        trace!("heads: {:?}", heads);
    }

    result
}
