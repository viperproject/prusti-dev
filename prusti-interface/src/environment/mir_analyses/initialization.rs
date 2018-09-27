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

use crate::utils::{self, is_prefix};
use csv::{ReaderBuilder, WriterBuilder};
use rustc::{hir, mir};
use std::collections::{HashMap, HashSet};
use std::env;
use std::mem;
use std::path::Path;
use rustc::ty::TyCtxt;
use rustc_data_structures::indexed_vec::Idx;

/// The set of initialized MIR places.
///
/// Invariant: we never have a place and any of its descendants in the
/// set at the same time. For example, having `x.f` and `x.f.g` in the
/// set at the same time is illegal.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PlaceSet<'tcx> {
    places: HashSet<mir::Place<'tcx>>,
}

impl<'tcx> PlaceSet<'tcx> {
    pub fn new() -> Self {
        Self {
            places: HashSet::new(),
        }
    }
    pub fn check_invariant(&self) {
        for place1 in self.places.iter() {
            for place2 in self.places.iter() {
                if place1 != place2 {
                    assert!(
                        !is_prefix(place1, place2),
                        "The place {:?} is a prefix of the place {:?}",
                        place2,
                        place1
                    );
                    assert!(
                        !is_prefix(place2, place1),
                        "The place {:?} is a prefix of the place {:?}",
                        place1,
                        place2
                    );
                }
            }
        }
    }
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a mir::Place<'tcx>> {
        self.places.iter()
    }
    /// Mark `place` as definitely initialized.
    pub fn set_initialized<'a>(
        &mut self,
        place: &mir::Place<'tcx>,
        mir: &mir::Mir<'tcx>,
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
    ) {
        self.check_invariant();
        // First, check that the place is not already marked as
        // definitely initialized.
        if !self.places.iter().any(|other| is_prefix(place, other)) {
            // To maintain the invariant that we do not have a place and its
            // prefix in the set, we remove all places for which the given
            // one is a prefix.
            self.places.retain(|other| !is_prefix(other, place));
            self.places.insert(place.clone());
            // If all fields of a struct are definitely initialized,
            // just keep info that the struct is definitely initialized.
            utils::collapse(mir, tcx, &mut self.places, place);
        }
        self.check_invariant();
    }
    /// Mark `place` as definitely uninitialized.
    pub fn set_uninitialized<'a>(
        &mut self,
        place: &mir::Place<'tcx>,
        mir: &mir::Mir<'tcx>,
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
    ) {
        self.check_invariant();
        let mut places = Vec::new();
        let old_places = mem::replace(&mut self.places, HashSet::new());
        // If needed, split the place whose part got uninitialized into
        // multiple places.
        for other in old_places.into_iter() {
            if is_prefix(place, &other) {
                // We are uninitializing a field of the place `other`.
                places.extend(utils::expand(mir, tcx, &other, place));
            } else if is_prefix(&other, place) {
                // We are uninitializing a place of which only some
                // fields are initialized. Just remove all initialized
                // fields.
                // This happens when the target place is already
                // initialized.
            } else {
                places.push(other);
            }
        }
        // Check the invariant.
        for place1 in places.iter() {
            assert!(
                !is_prefix(place1, place) && !is_prefix(place, place1),
                "Bug: failed to ensure that there are no prefixes: place={:?} place1={:?}",
                place,
                place1
            );
            for place2 in places.iter() {
                if place1 != place2 {
                    assert!(
                        !is_prefix(place1, place2),
                        "The place {:?} is a prefix of the place {:?}",
                        place2,
                        place1
                    );
                    assert!(
                        !is_prefix(place2, place1),
                        "The place {:?} is a prefix of the place {:?}",
                        place1,
                        place2
                    );
                }
            }
        }

        self.places = places.into_iter().collect();
        self.check_invariant();
    }
    /// Compute the intersection of the two place sets.
    pub fn merge(place_set1: &PlaceSet<'tcx>, place_set2: &PlaceSet<'tcx>) -> PlaceSet<'tcx> {
        place_set1.check_invariant();
        place_set2.check_invariant();
        let mut places = HashSet::new();
        let mut propage_places = |place_set1: &PlaceSet<'tcx>, place_set2: &PlaceSet<'tcx>| {
            for place in place_set1.iter() {
                for potential_prefix in place_set2.iter() {
                    if is_prefix(place, potential_prefix) {
                        places.insert(place.clone());
                        break;
                    }
                }
            }
        };
        propage_places(place_set1, place_set2);
        propage_places(place_set2, place_set1);
        let result = Self { places: places };
        result.check_invariant();
        result
    }
    /// This function fixes the invariant.
    pub fn deduplicate(&mut self) {
        let mut old_places = mem::replace(&mut self.places, HashSet::new());
        let mut places: Vec<_> = old_places.into_iter().collect();
        let mut to_remove = HashSet::new();
        for (i, place) in places.iter().enumerate() {
            for (j, other) in places.iter().enumerate() {
                if i <= j {
                    continue;
                }
                if place == other {
                    to_remove.insert(j);
                } else if is_prefix(place, other) {
                    to_remove.insert(i);
                } else if is_prefix(other, place) {
                    to_remove.insert(j);
                }
            }
        }
        for (i, place) in places.into_iter().enumerate() {
            if !to_remove.contains(&i) {
                self.places.insert(place);
            }
        }
        self.check_invariant();
    }
    /// Compute the union of the two place sets.
    ///
    /// Note that this function may break the invariant that we never
    /// have a place and its descendants in the set.
    pub fn union(place_set1: &PlaceSet<'tcx>, place_set2: &PlaceSet<'tcx>) -> PlaceSet<'tcx> {
        let mut places = place_set1.places.clone();
        places.extend(place_set2.iter().cloned());
        Self { places: places }
    }
}

/// The result of the definitely initialized analysis.
pub struct DefinitelyInitializedAnalysisResult<'tcx> {
    /// The state before the basic block.
    before_block: HashMap<mir::BasicBlock, PlaceSet<'tcx>>,
    /// The state after the statement.
    after_statement: HashMap<mir::Location, PlaceSet<'tcx>>,
}

impl<'tcx> DefinitelyInitializedAnalysisResult<'tcx> {
    pub fn new() -> Self {
        Self {
            before_block: HashMap::new(),
            after_statement: HashMap::new(),
        }
    }
    /// Get the initialization set before the first statement of the
    /// basic block.
    pub fn get_before_block(&self, bb: mir::BasicBlock) -> &PlaceSet<'tcx> {
        self.before_block
            .get(&bb)
            .expect(&format!("Missing initialization info for block {:?}", bb))
    }
    /// Get the initialization set after the statement.
    /// If `location.statement_index` is equal to the number of statements,
    /// returns the initialization set after the terminator.
    pub fn get_after_statement(&self, location: mir::Location) -> &PlaceSet {
        self.after_statement.get(&location).expect(&format!(
            "Missing initialization info for location {:?}",
            location
        ))
    }
}

/// A work item used in the fixpoint computation's work queue.
enum WorkItem {
    /// Need to apply the effects of the statement.
    ApplyStatementEffects(mir::Location),
    /// Need to apply the effects of the terminator.
    ApplyTerminatorEffects(mir::BasicBlock),
    /// Need to merge the incoming effects of multiple edges.
    MergeEffects(mir::BasicBlock),
}

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
            self.set_place_initialized(&mut place_set, &mir::Place::Local(arg));
        }
        self.result.before_block.insert(mir::START_BLOCK, place_set);
    }
    /// Add all statements to the work queue.
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
                counter <= 1000,
                "Definitely initialized analysis does not converge."
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
                self.set_place_initialized(&mut place_set, target);
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
                    self.set_place_uninitialized(&mut place_set, location);
                }
                mir::TerminatorKind::DropAndReplace {
                    ref location,
                    ref value,
                    ..
                } => {
                    self.set_place_uninitialized(&mut place_set, location);
                    self.apply_operand_effect(&mut place_set, value);
                    self.set_place_initialized(&mut place_set, location);
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
                        self.set_place_initialized(&mut place_set, place);
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
            let mut sets = self.mir.predecessors_for(bb);
            let mut sets = sets.iter();
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
    /// If the operand is move, make the place uninitialized.
    fn apply_operand_effect(&self, place_set: &mut PlaceSet<'tcx>, operand: &mir::Operand<'tcx>) {
        if let mir::Operand::Move(place) = operand {
            self.set_place_uninitialized(place_set, place);
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
    fn set_place_initialized(&self, place_set: &mut PlaceSet<'tcx>, place: &mir::Place<'tcx>) {
        place_set.set_initialized(place, self.mir, self.tcx);
    }
    /// Set `place` as uninitialized.
    fn set_place_uninitialized(&self, place_set: &mut PlaceSet<'tcx>, place: &mir::Place<'tcx>) {
        place_set.set_uninitialized(place, self.mir, self.tcx);
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
