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

use csv::{ReaderBuilder, WriterBuilder};
use rustc::{hir, mir};
use std::env;
use std::path::Path;
use rustc::ty::{self, TyCtxt};
use rustc_data_structures::indexed_vec::Idx;
use crate::environment::place_set::PlaceSet;
use super::common::{self, WorkItem};

/// The result of the definitely initialized analysis.
pub type DefinitelyInitializedAnalysisResult<'tcx> = common::AnalysisResult<PlaceSet<'tcx>>;

/// How place sets comming from different branches should be joined?
#[derive(Clone, Copy, Debug)]
enum JoinOperation {
    /// They should be intersected.
    Intersect,
    /// They should be unioned.
    Union,
}

/// Finds what places are definitely initialized at each MIR location.
struct DefinitelyInitializedAnalysis<'a, 'tcx: 'a> {
    result: DefinitelyInitializedAnalysisResult<'tcx>,
    /// Work queue.
    queue: Vec<WorkItem>,
    mir: &'a mir::Mir<'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    /// Should we intersect or union the incoming branches?
    ///
    /// We need first to compute the fix-point by using `Union` because
    /// otherwise when doing intersection at the loop head we always get
    /// too small definitely initialized sets. See `_test2` in
    /// `/tests/verify/pass/initialization/enums.rs`.
    join_operation: JoinOperation,
}

impl<'a, 'tcx: 'a> DefinitelyInitializedAnalysis<'a, 'tcx> {
    fn new(mir: &'a mir::Mir<'tcx>, tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        Self {
            result: DefinitelyInitializedAnalysisResult::new(),
            mir: mir,
            tcx: tcx,
            queue: Vec::new(),
            join_operation: JoinOperation::Intersect,
        }
    }
    /// Initialize all places to empty sets and mark that the arguments
    /// are definitely initialized at the entry point.
    fn initialize(&mut self) {
        for bb in self.mir.basic_blocks().indices() {
            self.result.before_block.insert(bb, PlaceSet::new());
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            for statement_index in 0..statements.len() + 1 {
                let location = mir::Location {
                    block: bb,
                    statement_index: statement_index,
                };
                self.result
                    .after_statement
                    .insert(location, PlaceSet::new());
            }
        }
        // Arguments are definitely initialized.
        let mut place_set = PlaceSet::new();
        for arg in self.mir.args_iter() {
            self.set_place_initialised(&mut place_set, &mir::Place::Local(arg));
        }
        self.result.before_block.insert(mir::START_BLOCK, place_set);
    }
    /// Add all statements to the work queue.
    /// TODO: Refactor to avoid code duplication with liveness analysis.
    fn propagate_work_queue(&mut self) {
        for bb in self.mir.basic_blocks().indices() {
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            self.queue.push(WorkItem::MergeEffects(bb));
            for statement_index in 0..statements.len() + 1 {
                let location = mir::Location {
                    block: bb,
                    statement_index: statement_index,
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
    fn run(&mut self, join_operation: JoinOperation) {
        trace!("[enter] run join_operation={:?}", join_operation);
        self.join_operation = join_operation;
        let mut counter = 0; // For debugging.
        while let Some(work_item) = self.queue.pop() {
            assert!(
                counter <= 1000000,
                "Definitely initialized analysis (initialization) does not converge."
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
        self.compute_return_state();
    }
    /// Apply the effects of the statement to the place set. If the effect
    /// changes the place set, add the following statement or terminator
    /// to the work queue.
    fn apply_statement_effects(&mut self, location: mir::Location) {
        trace!("[enter] apply_statement_effects location={:?}", location);
        let statement = &self.mir[location.block].statements[location.statement_index];
        let mut place_set = self.get_place_set_before_statement(location);
        match statement.kind {
            mir::StatementKind::Assign(ref target, ref source) => {
                match source {
                    mir::Rvalue::Repeat(ref operand, _)
                    | mir::Rvalue::Cast(_, ref operand, _)
                    | mir::Rvalue::UnaryOp(_, ref operand)
                    | mir::Rvalue::Use(ref operand) => {
                        self.apply_operand_effect(&mut place_set, operand);
                    }
                    mir::Rvalue::BinaryOp(_, ref operand1, ref operand2)
                    | mir::Rvalue::CheckedBinaryOp(_, ref operand1, ref operand2) => {
                        self.apply_operand_effect(&mut place_set, operand1);
                        self.apply_operand_effect(&mut place_set, operand2);
                    }
                    mir::Rvalue::Aggregate(_, ref operands) => for operand in operands.iter() {
                        self.apply_operand_effect(&mut place_set, operand);
                    },
                    _ => {}
                }
                self.set_place_initialised(&mut place_set, target);
            }
            _ => {}
        }
        self.update_place_set_after_statement(location, place_set);
    }
    /// Apply the effects of the terminator to the place set. If the effect
    /// changes the place set, add all reachable basic blocks to the work
    /// queue.
    fn apply_terminator_effects(&mut self, bb: mir::BasicBlock) {
        trace!("[enter] apply_terminator_effects bb={:?}", bb);
        let mir::BasicBlockData { ref terminator, .. } = self.mir[bb];
        let mut place_set = self.get_place_set_before_terminator(bb);
        if let Some(ref terminator) = *terminator {
            match terminator.kind {
                mir::TerminatorKind::SwitchInt { ref discr, .. } => {
                    self.apply_operand_effect(&mut place_set, discr);
                }
                mir::TerminatorKind::Drop { ref location, .. } => {
                    self.set_place_uninitialised(&mut place_set, location);
                }
                mir::TerminatorKind::DropAndReplace {
                    ref location,
                    ref value,
                    ..
                } => {
                    self.set_place_uninitialised(&mut place_set, location);
                    self.apply_operand_effect(&mut place_set, value);
                    self.set_place_initialised(&mut place_set, location);
                }
                mir::TerminatorKind::Call {
                    ref func,
                    ref args,
                    ref destination,
                    ..
                } => {
                    self.apply_operand_effect(&mut place_set, func);
                    for arg in args.iter() {
                        self.apply_operand_effect(&mut place_set, arg);
                    }
                    if let Some((place, _)) = destination {
                        self.set_place_initialised(&mut place_set, place);
                    }
                }
                mir::TerminatorKind::Assert { ref cond, .. } => {
                    self.apply_operand_effect(&mut place_set, cond);
                }
                mir::TerminatorKind::Yield { ref value, .. } => {
                    self.apply_operand_effect(&mut place_set, value);
                }
                _ => {}
            }
        }
        let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
        let location = mir::Location {
            block: bb,
            statement_index: statements.len(),
        };
        self.update_place_set_after_statement(location, place_set);
    }
    /// Merge place sets of the incoming basic blocks. If the target
    /// place set changed, add the first statement of the block to the
    /// work queue.
    fn merge_effects(&mut self, bb: mir::BasicBlock) {
        trace!("[enter] merge_effects bb={:?}", bb);
        let place_set = {
            let sets = self.mir.predecessors_for(bb);
            let sets = sets.iter();
            let mut sets = sets.map(|&predecessor| self.get_place_set_after_block(predecessor));
            if let Some(first) = sets.next() {
                match self.join_operation {
                    JoinOperation::Intersect => {
                        sets.fold(first, |acc, set| PlaceSet::merge(&acc, &set))
                    }
                    JoinOperation::Union => {
                        let mut place_set =
                            sets.fold(first, |acc, set| PlaceSet::union(&acc, &set));
                        place_set.deduplicate();
                        place_set
                    }
                }
            } else {
                return;
            }
        };
        let changed = {
            let old_place_set = &self.result.before_block[&bb];
            trace!(
                "    merge_effects bb={:?} old_place_set={:?} place_set={:?}",
                bb,
                old_place_set,
                place_set
            );
            old_place_set != &place_set
        };
        if changed {
            self.result.before_block.insert(bb, place_set);
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            if statements.len() == 0 {
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
    /// Compute the initiliasation state at the function return.
    fn compute_return_state(&mut self) {
        let mut sets = self.mir.basic_blocks()
            .iter_enumerated()
            .filter(|(_, bb)| {
                if let mir::TerminatorKind::Return = bb.terminator().kind {
                    true
                } else {
                    false
                }
            })
            .map(|(bbi, _)| self.get_place_set_after_block(bbi));
        if let Some(first) = sets.next() {
            self.result.at_return = sets.fold(first, |acc, set| PlaceSet::merge(&acc, &set));
        }
    }
    /// If the operand is move, make the place uninitialized.
    fn apply_operand_effect(&self, place_set: &mut PlaceSet<'tcx>, operand: &mir::Operand<'tcx>) {
        if let mir::Operand::Move(place) = operand {
            match place.ty(self.mir, self.tcx) {
                mir::tcx::PlaceTy::Ty { ty: ty::TyS {
                    sty: ty::TypeVariants::TyRef(_, _, _),
                    ..
                }} => {
                    // We do not set references as uninitialised. See issue #119.
                },
                _ => {
                    self.set_place_uninitialised(place_set, place);
                }
            }
        }
    }
    /// Return the place set before the given statement.
    fn get_place_set_before_statement(&self, mut location: mir::Location) -> PlaceSet<'tcx> {
        if location.statement_index == 0 {
            self.result.before_block[&location.block].clone()
        } else {
            location.statement_index -= 1;
            self.result.after_statement[&location].clone()
        }
    }
    /// Return the place set before the terminator of the given basic block.
    fn get_place_set_before_terminator(&self, bb: mir::BasicBlock) -> PlaceSet<'tcx> {
        let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
        if statements.len() == 0 {
            self.result.before_block[&bb].clone()
        } else {
            let location = mir::Location {
                block: bb,
                statement_index: statements.len() - 1,
            };
            self.result.after_statement[&location].clone()
        }
    }
    /// Return the place set after the given basic block.
    fn get_place_set_after_block(&self, bb: mir::BasicBlock) -> PlaceSet<'tcx> {
        let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
        let location = mir::Location {
            block: bb,
            statement_index: statements.len(),
        };
        self.result.after_statement[&location].clone()
    }
    /// If the place set after the statement is different from the provided,
    /// updates it and adds the successor to the work queue.
    fn update_place_set_after_statement(
        &mut self,
        mut location: mir::Location,
        place_set: PlaceSet<'tcx>,
    ) {
        let changed = {
            let old_place_set = &self.result.after_statement[&location];
            old_place_set != &place_set
        };
        if changed {
            self.result.after_statement.insert(location, place_set);
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
    /// Set `place` as definitely initialized.
    fn set_place_initialised(&self, place_set: &mut PlaceSet<'tcx>, place: &mir::Place<'tcx>) {
        place_set.insert(place, self.mir, self.tcx);
    }
    /// Set `place` as uninitialized.
    fn set_place_uninitialised(&self, place_set: &mut PlaceSet<'tcx>, place: &mir::Place<'tcx>) {
        place_set.remove(place, self.mir, self.tcx);
    }
}

/// Compute the which places are definitely initialized at each program
/// point.
pub fn compute_definitely_initialized<'a, 'tcx: 'a>(
    mir: &'a mir::Mir<'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    def_path: hir::map::DefPath,
) -> DefinitelyInitializedAnalysisResult<'tcx> {
    let mut analysis = DefinitelyInitializedAnalysis::new(mir, tcx);
    analysis.initialize();
    analysis.propagate_work_queue();
    analysis.run(JoinOperation::Union);
    analysis.propagate_work_queue();
    analysis.run(JoinOperation::Intersect);
    if let Ok(path) = env::var("PRUSTI_TEST_FILE") {
        // We are running tests, compare computed initialization results
        // with the expected ones.
        analysis.result.compare_with_expected(def_path, path);
    }
    analysis.result
}

#[derive(Debug, Serialize, Deserialize, Ord, PartialOrd, Eq, PartialEq)]
/// A record for serializing definitely initialized info into a file for testing.
struct InitializationRecord {
    block: usize,
    /// -1 indicates before the block.
    statement_index: isize,
    /// A String representation of a place set.
    places: String,
}

impl InitializationRecord {
    fn new(block: mir::BasicBlock, statement_index: isize, place_set: &PlaceSet) -> Self {
        let mut places: Vec<_> = place_set
            .iter()
            .map(|place| format!("{:?}", place))
            .collect();
        places.sort();
        Self {
            block: block.index(),
            statement_index: statement_index,
            places: places.join(", "),
        }
    }
}

impl<'tcx> DefinitelyInitializedAnalysisResult<'tcx> {
    /// Converts to a sorted vector of `InitializationRecord`.
    fn to_initialization_records(&self) -> Vec<InitializationRecord> {
        let mut records = Vec::new();
        for (bb, place_set) in self.before_block.iter() {
            records.push(InitializationRecord::new(*bb, -1, place_set));
        }
        for (location, place_set) in self.after_statement.iter() {
            records.push(InitializationRecord::new(
                location.block,
                location.statement_index as isize,
                place_set,
            ));
        }
        records.sort();
        records
    }
    /// Compare the expected analysis results with the actual.
    fn compare_with_expected(&self, def_path: hir::map::DefPath, test_file: String) {
        trace!(
            "[enter] compare_definitely_initialized def_path={:?} test_file={}",
            def_path,
            test_file
        );
        let mut expected_result_file = test_file.clone();
        expected_result_file.push('.');
        expected_result_file.push_str(&def_path.to_filename_friendly_no_crate());
        expected_result_file.push('.');
        expected_result_file.push_str("def_init");
        let expected_result_path = Path::new(&expected_result_file);

        trace!("expected_result_file={}", expected_result_file);
        if !expected_result_path.exists() {
            return;
        }
        let actual_result = self.to_initialization_records();

        let mut reader = ReaderBuilder::new()
            .from_path(&expected_result_path)
            .unwrap();
        let mut expected_result = Vec::new();
        for row in reader.deserialize() {
            let record = row.unwrap();
            expected_result.push(record);
        }
        if actual_result != expected_result {
            let mut actual_result_file = expected_result_file.clone();
            actual_result_file.push_str(".actual");
            let actual_result_path = Path::new(&actual_result_file);

            let mut writer = WriterBuilder::new().from_path(&actual_result_path).unwrap();
            for record in actual_result {
                writer.serialize(record).unwrap();
            }

            panic!(
                "Expected ({:?}) definitely initialized information differ from actual ({:?}).",
                expected_result_file, actual_result_file
            );
        }

        trace!("[exit] compare_definitely_initialized");
    }
}
