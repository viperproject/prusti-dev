// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::mir;
use std::collections::HashMap;

pub struct AnalysisResult<T> {
    /// The state before the basic block.
    pub before_block: HashMap<mir::BasicBlock, T>,
    /// The state after the statement.
    pub after_statement: HashMap<mir::Location, T>,
}

impl<T> AnalysisResult<T> {
    pub fn new() -> Self {
        Self {
            before_block: HashMap::new(),
            after_statement: HashMap::new(),
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
        self.after_statement.get(&location).unwrap_or_else(|| panic!("Missing initialization info for location {:?}",
            location))
    }
}

/// A work item used in the fixpoint computation's work queue.
pub(super) enum WorkItem {
    /// Need to apply the effects of the statement.
    ApplyStatementEffects(mir::Location),
    /// Need to apply the effects of the terminator.
    ApplyTerminatorEffects(mir::BasicBlock),
    /// Need to merge the incoming effects of multiple edges.
    MergeEffects(mir::BasicBlock),
}
