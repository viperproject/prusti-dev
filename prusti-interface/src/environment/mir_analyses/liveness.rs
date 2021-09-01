// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module provides the liveness analysis for MIR.
//!
//! It computes for each program point which assignments to local
//! variables may reach that program point.

use super::common::{self, WorkItem};
use rustc_middle::mir;
use std::collections::BTreeSet;
use std::fmt;
use log::trace;

#[derive(PartialEq, Eq, Hash, Copy, Clone, Ord, PartialOrd)]
pub struct Assignment {
    pub target: mir::Local,
    pub location: mir::Location,
}

impl fmt::Debug for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}={:?}", self.target, self.location)
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct AssignmentSet {
    set: BTreeSet<Assignment>,
}

impl AssignmentSet {
    fn new() -> Self {
        Self {
            set: BTreeSet::new(),
        }
    }
    fn union(sets: Vec<&Self>) -> Self {
        let mut union_set = BTreeSet::new();
        for set in &sets {
            union_set.extend(set.iter())
        }
        Self {
            set: union_set,
        }
    }
    fn replace(&mut self, local: mir::Local, location: mir::Location) {
        self.set = self
            .set
            .iter()
            .filter(|assignment| assignment.target != local)
            .cloned()
            .collect();
        self.set.insert(Assignment {
            target: local,
            location,
        });
    }
    pub fn iter(&self) -> impl Iterator<Item = &Assignment> {
        self.set.iter()
    }
}

/// The result of the liveness analysis.
pub type LivenessAnalysisResult = common::AnalysisResult<AssignmentSet>;

/// Finds which assignments are live at which program points.
struct LivenessAnalysis<'a, 'tcx: 'a> {
    result: LivenessAnalysisResult,
    mir: &'a mir::Body<'tcx>,
    /// Work queue.
    queue: Vec<WorkItem>,
}

impl<'a, 'tcx: 'a> LivenessAnalysis<'a, 'tcx> {
    fn new(mir: &'a mir::Body<'tcx>) -> Self {
        Self {
            result: LivenessAnalysisResult::new(),
            mir,
            queue: Vec::new(),
        }
    }
    /// Initialise all places to empty sets.
    fn initialize(&mut self) {
        for bb in self.mir.basic_blocks().indices() {
            self.result.before_block.insert(bb, AssignmentSet::new());
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            for statement_index in 0..statements.len() + 1 {
                let location = mir::Location {
                    block: bb,
                    statement_index,
                };
                self.result
                    .after_statement
                    .insert(location, AssignmentSet::new());
            }
        }
    }
    /// Add all statements to the work queue.
    /// TODO: Refactor to avoid code duplication with initialisation analysis.
    fn propagate_work_queue(&mut self) {
        for bb in self.mir.basic_blocks().indices() {
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            self.queue.push(WorkItem::MergeEffects(bb));
            for statement_index in 0..statements.len() + 1 {
                let location = mir::Location {
                    block: bb,
                    statement_index,
                };
                if statement_index != statements.len() {
                    self.queue.push(WorkItem::ApplyStatementEffects(location));
                } else {
                    self.queue.push(WorkItem::ApplyTerminatorEffects(bb));
                }
            }
        }
        self.queue.reverse();
    }
    /// Run the analysis up to a fix-point.
    fn run(&mut self) {
        trace!("[enter] run");
        let mut counter = 0; // For debugging.
        while let Some(work_item) = self.queue.pop() {
            assert!(
                counter <= 1000000,
                "Definitely initialized analysis (liveness) does not converge."
            );
            match work_item {
                WorkItem::ApplyStatementEffects(location) => {
                    self.apply_statement_effects(location);
                }
                WorkItem::ApplyTerminatorEffects(bb) => {
                    self.apply_terminator_effects(bb);
                }
                WorkItem::MergeEffects(bb) => {
                    self.merge_effects(bb);
                }
            }
            counter += 1;
        }
    }
    /// Apply the effects of the statement to the assignment set. If the effect
    /// changes the assignment set, add the following statement or terminator
    /// to the work queue.
    fn apply_statement_effects(&mut self, location: mir::Location) {
        trace!("[enter] apply_statement_effects location={:?}", location);
        let statement = &self.mir[location.block].statements[location.statement_index];
        let mut set = self.get_set_before_statement(location);
        if let mir::StatementKind::Assign(box (ref target, _)) = statement.kind {
            self.replace_in_set(&mut set, target, location);
        }
        self.update_set_after_statement(location, set);
    }
    /// Apply the effects of the terminator to the assignment set. If
    /// the effect changes the set, add all reachable basic blocks to the
    /// work queue.
    fn apply_terminator_effects(&mut self, bb: mir::BasicBlock) {
        trace!("[enter] apply_terminator_effects bb={:?}", bb);
        let mir::BasicBlockData {
            ref terminator,
            ref statements,
            ..
        } = self.mir[bb];
        let mut set = self.get_set_before_terminator(bb);
        if let Some(terminator) = terminator {
            if let mir::TerminatorKind::Call {
                destination: Some((place, _)), ..
            } = &terminator.kind {
                let location = mir::Location {
                    block: bb,
                    statement_index: statements.len(),
                };
                self.replace_in_set(&mut set, place, location);
            }
        }
        let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
        let location = mir::Location {
            block: bb,
            statement_index: statements.len(),
        };
        self.update_set_after_statement(location, set);
    }
    /// Merge sets of the incoming basic blocks. If the target
    /// set changed, add the first statement of the block to the
    /// work queue.
    fn merge_effects(&mut self, bb: mir::BasicBlock) {
        trace!("[enter] merge_effects bb={:?}", bb);
        let set = {
            let sets = &self.mir.predecessors()[bb];
            if sets.is_empty() {
                return;
            }
            AssignmentSet::union(
                sets.iter().map(|&predecessor| self.get_set_after_block(predecessor)).collect()
            )
        };
        let changed = {
            let old_set = &self.result.before_block[&bb];
            trace!(
                "    merge_effects bb={:?} old_set={:?} set={:?}",
                bb,
                old_set,
                set
            );
            old_set != &set
        };
        if changed {
            self.result.before_block.insert(bb, set);
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            if statements.is_empty() {
                self.queue.push(WorkItem::ApplyTerminatorEffects(bb));
            } else {
                let location = mir::Location {
                    block: bb,
                    statement_index: 0,
                };
                self.queue.push(WorkItem::ApplyStatementEffects(location));
            }
        }
    }
    /// Replace all assignments to `place` as definitely initialized.
    fn replace_in_set(
        &self,
        set: &mut AssignmentSet,
        place: &mir::Place<'tcx>,
        location: mir::Location,
    ) {
        // FIXME: Potential wrong.
        if place.projection.is_empty() {
        // if let mir::Place::Local(ref local) = place {
            set.replace(place.local, location);
        }
    }
    /// If the place set after the statement is different from the provided,
    /// updates it and adds the successor to the work queue.
    fn update_set_after_statement(&mut self, mut location: mir::Location, set: AssignmentSet) {
        let changed = {
            let old_set = &self.result.after_statement[&location];
            old_set != &set
        };
        if changed {
            self.result.after_statement.insert(location, set);
            let mir::BasicBlockData {
                ref statements,
                ref terminator,
                ..
            } = self.mir[location.block];
            if location.statement_index + 1 == statements.len() {
                // The next statement is terminator.
                self.queue
                    .push(WorkItem::ApplyTerminatorEffects(location.block));
            } else if location.statement_index == statements.len() {
                // We just updated the terminator, need to update all successors.
                for successor in terminator.as_ref().unwrap().successors() {
                    self.queue.push(WorkItem::MergeEffects(*successor));
                }
            } else {
                location.statement_index += 1;
                self.queue.push(WorkItem::ApplyStatementEffects(location));
            }
        }
    }
    /// Return the set before the given statement.
    fn get_set_before_statement(&self, mut location: mir::Location) -> AssignmentSet {
        if location.statement_index == 0 {
            self.result.before_block[&location.block].clone()
        } else {
            location.statement_index -= 1;
            self.result.after_statement[&location].clone()
        }
    }
    /// Return the set before the terminator of the given basic block.
    fn get_set_before_terminator(&self, bb: mir::BasicBlock) -> AssignmentSet {
        let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
        if statements.is_empty() {
            self.result.before_block[&bb].clone()
        } else {
            let location = mir::Location {
                block: bb,
                statement_index: statements.len() - 1,
            };
            self.result.after_statement[&location].clone()
        }
    }
    /// Return the set after the given basic block.
    fn get_set_after_block(&self, bb: mir::BasicBlock) -> &AssignmentSet {
        let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
        let location = mir::Location {
            block: bb,
            statement_index: statements.len(),
        };
        &self.result.after_statement[&location]
    }
}

/// Compute which assignments to local variables are live at each
/// program point.
pub fn compute_liveness<'a, 'tcx: 'a>(mir: &'a mir::Body<'tcx>) -> LivenessAnalysisResult {
    let mut analysis = LivenessAnalysis::new(mir);
    analysis.initialize();
    analysis.propagate_work_queue();
    analysis.run();
    analysis.result
}
