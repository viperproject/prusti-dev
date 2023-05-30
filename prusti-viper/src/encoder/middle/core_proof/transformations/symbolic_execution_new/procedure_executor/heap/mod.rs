use self::{
    close_frac_ref::ClosedFracRef,
    common::{AliasedWholeBool, FindSnapshotResult, NamedPredicateInstances, NoSnapshot},
    dead_lifetimes::DeadLifetimeTokens,
    global_heap_state::HeapVariables,
    lifetimes::LifetimeTokens,
    memory_block::MemoryBlock,
    owned::Owned,
};
use super::{
    super::super::encoder_context::EncoderContext,
    constraints::{BlockConstraints, ConstraintsMergeReport},
    ProcedureExecutor,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution_new::{
        expression_interner::ExpressionInterner, program_context::ProgramContext,
    },
};
use std::collections::{BTreeMap, BTreeSet};
use vir_crate::{
    common::builtin_constants::MEMORY_BLOCK_PREDICATE_NAME,
    low::{self as vir_low},
};

mod common;
mod lifetimes;
mod dead_lifetimes;
mod owned;
mod memory_block;
mod close_frac_ref;
// mod snapshots;
mod utils;
mod purification;
mod merge_report;
mod global_heap_state;

pub(super) use self::{
    global_heap_state::GlobalHeapState,
    merge_report::HeapMergeReport,
    purification::{PurificationResult, SnapshotBinding},
};

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn save_state(&mut self, label: String) -> SpannedEncodingResult<()> {
        let current_block = self.current_block.as_ref().unwrap();
        let current_state = self.state_keeper.get_state_mut(current_block);
        self.global_heap_state.insert(label, &current_state.heap)?;
        Ok(())
    }

    /// Should be called only by simplify_expression.
    pub(super) fn purify_snap_function_calls(
        &mut self,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<PurificationResult> {
        let current_block = self.current_block.as_ref().unwrap();
        let current_state = self.state_keeper.get_state_mut(current_block);
        self::purification::purify_snap_function_calls(
            &current_state.heap,
            &mut self.global_heap_state,
            self.program_context,
            &mut current_state.constraints,
            &mut self.expression_interner,
            expression.clone(),
        )
    }

    /// FIXME: Since the code is incomplete, we temporarily return a boolean to
    /// indicate whether the predicate was handled.
    pub(super) fn inhale_predicate(
        &mut self,
        predicate: vir_low::ast::expression::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let current_block = self.current_block.as_ref().unwrap();
        let current_state = self.state_keeper.get_state_mut(current_block);
        let block_builder = self.current_block_builder.as_mut().unwrap();
        block_builder.add_statement(vir_low::Statement::comment(format!("inhale {predicate}")))?;
        match self.program_context.get_predicate_kind(&predicate.name) {
            vir_low::PredicateKind::MemoryBlock => {
                current_state.heap.memory_block.inhale(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
            }
            vir_low::PredicateKind::Owned => {
                current_state.heap.owned.inhale(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
            }
            vir_low::PredicateKind::LifetimeToken => {
                current_state.heap.lifetimes.inhale(
                    predicate,
                    position,
                    &current_state.constraints,
                    block_builder,
                )?;
            }
            vir_low::PredicateKind::DeadLifetimeToken => {
                // current_state.heap.dead_lifetimes.inhale(
                //     predicate,
                //     position,
                //     &mut current_state.constraints,
                //     block_builder,
                // )?;
                current_state.heap.dead_lifetimes.inhale(
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    block_builder,
                )?;
                // current_state.heap.dead_lifetimes.inhale(
                //     self.program_context,
                //     &mut self.expression_interner,
                //     &mut self.global_heap_state,
                //     predicate,
                //     position,
                //     &mut current_state.constraints,
                //     block_builder,
                // )?;
            }
            vir_low::PredicateKind::CloseFracRef => {
                current_state.heap.close_frac_ref.inhale(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
            }
            // vir_low::PredicateKind::WithoutSnapshotFrac => {
            //     current_state.heap.without_snapshot_frac.inhale(
            //         self.program_context,
            //         &mut self.expression_interner,
            //         &mut self.global_heap_state,
            //         predicate,
            //         position,
            //         &mut current_state.constraints,
            //         block_builder,
            //     )?;
            // }
            vir_low::PredicateKind::WithoutSnapshotWhole => {
                current_state.heap.without_snapshot_whole.inhale(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
            }
            vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => {
                current_state
                    .heap
                    .without_snapshot_whole_non_aliased
                    .inhale(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                    )?;
            }
            vir_low::PredicateKind::EndBorrowViewShift => {
                current_state
                    .heap
                    .without_snapshot_whole_non_aliased
                    .inhale(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                    )?;
            }
        };
        Ok(())
    }

    /// FIXME: Since the code is incomplete, we temporarily return a boolean to
    /// indicate whether the predicate was handled.
    pub(super) fn exhale_predicate(
        &mut self,
        predicate: vir_low::ast::expression::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let current_block = self.current_block.as_ref().unwrap();
        let current_state = self.state_keeper.get_state_mut(current_block);
        let block_builder = self.current_block_builder.as_mut().unwrap();
        block_builder.add_statement(vir_low::Statement::comment(format!("exhale {predicate}")))?;
        match self.program_context.get_predicate_kind(&predicate.name) {
            vir_low::PredicateKind::MemoryBlock => {
                current_state.heap.memory_block.exhale(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
            }
            vir_low::PredicateKind::Owned => {
                current_state.heap.owned.exhale(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
            }
            vir_low::PredicateKind::LifetimeToken => {
                current_state.heap.lifetimes.exhale(
                    predicate,
                    position,
                    &current_state.constraints,
                    block_builder,
                )?;
            }
            vir_low::PredicateKind::DeadLifetimeToken => {
                // current_state.heap.dead_lifetimes.exhale(
                //     predicate,
                //     position,
                //     &current_state.constraints,
                //     block_builder,
                // )?;
                current_state.heap.dead_lifetimes.exhale(
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
                // current_state.heap.dead_lifetimes.exhale(
                //     self.program_context,
                //     &mut self.expression_interner,
                //     &mut self.global_heap_state,
                //     predicate,
                //     position,
                //     &mut current_state.constraints,
                //     block_builder,
                // )?;
            }
            vir_low::PredicateKind::CloseFracRef => {
                current_state.heap.close_frac_ref.exhale(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
            }
            // vir_low::PredicateKind::WithoutSnapshotFrac => {
            //     current_state.heap.without_snapshot_frac.exhale(
            //         self.program_context,
            //         &mut self.expression_interner,
            //         &mut self.global_heap_state,
            //         predicate,
            //         position,
            //         &mut current_state.constraints,
            //         block_builder,
            //     )?;
            // }
            vir_low::PredicateKind::WithoutSnapshotWhole => {
                current_state.heap.without_snapshot_whole.exhale(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
            }
            vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => {
                current_state
                    .heap
                    .without_snapshot_whole_non_aliased
                    .exhale(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                    )?;
            }
            vir_low::PredicateKind::EndBorrowViewShift => {
                current_state
                    .heap
                    .without_snapshot_whole_non_aliased
                    .exhale(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                    )?;
            }
        };
        Ok(())
    }

    pub(super) fn materialize_predicate(
        &mut self,
        predicate: vir_low::ast::expression::PredicateAccessPredicate,
        check_that_exists: bool,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let current_block = self.current_block.as_ref().unwrap();
        let current_state = self.state_keeper.get_state_mut(current_block);
        let block_builder = self.current_block_builder.as_mut().unwrap();
        block_builder.add_statement(vir_low::Statement::comment(format!(
            "materialize {predicate}"
        )))?;
        match self.program_context.get_predicate_kind(&predicate.name) {
            vir_low::PredicateKind::MemoryBlock => {
                current_state.heap.memory_block.materialize(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                    check_that_exists,
                )?;
            }
            vir_low::PredicateKind::Owned => {
                current_state.heap.owned.materialize(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                    check_that_exists,
                )?;
            }
            vir_low::PredicateKind::LifetimeToken => {
                unreachable!();
            }
            vir_low::PredicateKind::DeadLifetimeToken => {
                unreachable!();
            }
            vir_low::PredicateKind::CloseFracRef => {
                current_state.heap.close_frac_ref.materialize(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                    check_that_exists,
                )?;
            }
            // vir_low::PredicateKind::WithoutSnapshotFrac => {
            //     current_state.heap.without_snapshot_frac.materialize(
            //         self.program_context,
            //         &mut self.expression_interner,
            //         &mut self.global_heap_state,
            //         predicate,
            //         position,
            //         &mut current_state.constraints,
            //         block_builder,
            //     )?;
            // }
            vir_low::PredicateKind::WithoutSnapshotWhole => {
                current_state.heap.without_snapshot_whole.materialize(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                    check_that_exists,
                )?;
            }
            vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => {
                current_state
                    .heap
                    .without_snapshot_whole_non_aliased
                    .materialize(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                        check_that_exists,
                    )?;
            }
            vir_low::PredicateKind::EndBorrowViewShift => {
                current_state
                    .heap
                    .without_snapshot_whole_non_aliased
                    .materialize(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                        check_that_exists,
                    )?;
            }
        };
        Ok(())
    }

    // pub(super) fn mark_predicate_instances_seen_qp_inhale(
    //     &mut self,
    //     _predicate_name: &str,
    // ) -> SpannedEncodingResult<()> {
    //     // FIXME: Implement
    //     Ok(())
    // }

    /// We have an untracked exhale, materialize all affected predicates.
    pub(super) fn prepare_for_unhandled_exhale(
        &mut self,
        predicate_name: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let current_block = self.current_block.as_ref().unwrap();
        let current_state = self.state_keeper.get_state_mut(current_block);
        let block_builder = self.current_block_builder.as_mut().unwrap();
        match self.program_context.get_predicate_kind(predicate_name) {
            vir_low::PredicateKind::MemoryBlock => {
                current_state
                    .heap
                    .memory_block
                    .prepare_for_unhandled_exhale(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate_name,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                    )?;
            }
            vir_low::PredicateKind::Owned => {
                current_state.heap.owned.prepare_for_unhandled_exhale(
                    self.program_context,
                    &mut self.expression_interner,
                    &mut self.global_heap_state,
                    predicate_name,
                    position,
                    &mut current_state.constraints,
                    block_builder,
                )?;
            }
            vir_low::PredicateKind::LifetimeToken => {
                unreachable!();
            }
            vir_low::PredicateKind::DeadLifetimeToken => {
                unreachable!();
            }
            vir_low::PredicateKind::CloseFracRef => {
                unreachable!();
            }
            // vir_low::PredicateKind::WithoutSnapshotFrac => {
            //     current_state
            //         .heap
            //         .without_snapshot_frac
            //         .prepare_for_unhandled_exhale(
            //             self.program_context,
            //             &mut self.expression_interner,
            //             &mut self.global_heap_state,
            //             predicate_name,
            //             position,
            //             &mut current_state.constraints,
            //             block_builder,
            //         )?;
            // }
            vir_low::PredicateKind::WithoutSnapshotWhole => {
                current_state
                    .heap
                    .without_snapshot_whole
                    .prepare_for_unhandled_exhale(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate_name,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                    )?;
            }
            vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => {
                current_state
                    .heap
                    .without_snapshot_whole_non_aliased
                    .prepare_for_unhandled_exhale(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate_name,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                    )?;
            }
            vir_low::PredicateKind::EndBorrowViewShift => {
                current_state
                    .heap
                    .without_snapshot_whole_non_aliased
                    .prepare_for_unhandled_exhale(
                        self.program_context,
                        &mut self.expression_interner,
                        &mut self.global_heap_state,
                        predicate_name,
                        position,
                        &mut current_state.constraints,
                        block_builder,
                    )?;
            }
        };
        Ok(())
    }
}

#[derive(Default, Clone)]
pub(super) struct BlockHeap {
    lifetimes: LifetimeTokens<false>,
    // dead_lifetimes: LifetimeTokens<true>,
    dead_lifetimes: DeadLifetimeTokens,
    owned: Owned,
    memory_block: MemoryBlock,
    close_frac_ref: ClosedFracRef,
    // without_snapshot_frac: NamedPredicateInstances<AliasedFractionalBoundedPerm, NoSnapshot>,
    without_snapshot_whole: NamedPredicateInstances<AliasedWholeBool, NoSnapshot>,
    without_snapshot_whole_non_aliased: NamedPredicateInstances<AliasedWholeBool, NoSnapshot>,
    // dead_lifetimes: NamedPredicateInstances<AliasedWholeNat, NoSnapshot>,
}

impl std::fmt::Display for BlockHeap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "lifetimes: {}", self.lifetimes)?;
        writeln!(f, "owned: {}", self.owned)?;
        writeln!(f, "memory_block: {}", self.memory_block)?;
        writeln!(f, "close_frac_ref: {}", self.close_frac_ref)?;
        // writeln!(f, "without_snapshot_frac: {}", self.without_snapshot_frac)?;
        writeln!(f, "without_snapshot_whole: {}", self.without_snapshot_whole)?;
        writeln!(
            f,
            "without_snapshot_whole_non_aliased: {}",
            self.without_snapshot_whole_non_aliased
        )?;
        writeln!(f, "dead_lifetimes: {}", self.dead_lifetimes)?;
        Ok(())
    }
}

impl BlockHeap {
    pub(super) fn merge(
        &mut self,
        other: &Self,
        self_edge_block: &mut Vec<vir_low::Statement>,
        other_edge_block: &mut Vec<vir_low::Statement>,
        position: vir_low::Position,
        constraints_merge_report: ConstraintsMergeReport,
        heap_merge_report: &mut HeapMergeReport,
        constraints: &mut BlockConstraints,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        self.lifetimes
            .merge(&other.lifetimes, &constraints_merge_report)?;
        // self.dead_lifetimes
        //     .merge(&other.dead_lifetimes, &constraints_merge_report)?;
        self.dead_lifetimes
            .merge(&other.dead_lifetimes, heap_merge_report, global_state)?;
        self.owned.merge(
            &other.owned,
            self_edge_block,
            other_edge_block,
            position,
            heap_merge_report,
            constraints,
            &constraints_merge_report,
            expression_interner,
            program_context,
            global_state,
        )?;
        self.memory_block.merge(
            &other.memory_block,
            self_edge_block,
            other_edge_block,
            position,
            heap_merge_report,
            constraints,
            &constraints_merge_report,
            expression_interner,
            program_context,
            global_state,
        )?;
        self.close_frac_ref.merge(
            &other.close_frac_ref,
            self_edge_block,
            other_edge_block,
            position,
            heap_merge_report,
            constraints,
            &constraints_merge_report,
            expression_interner,
            program_context,
            global_state,
        )?;
        // self.without_snapshot_frac.merge(
        //     &other.without_snapshot_frac,
        //     self_edge_block,
        //     other_edge_block,
        //     position,
        //     heap_merge_report,
        //     constraints,
        //     &constraints_merge_report,
        //     expression_interner,
        //     program_context,
        //     global_state,
        // )?;
        self.without_snapshot_whole.merge(
            &other.without_snapshot_whole,
            self_edge_block,
            other_edge_block,
            position,
            heap_merge_report,
            constraints,
            &constraints_merge_report,
            expression_interner,
            program_context,
            global_state,
        )?;
        self.without_snapshot_whole_non_aliased.merge(
            &other.without_snapshot_whole_non_aliased,
            self_edge_block,
            other_edge_block,
            position,
            heap_merge_report,
            constraints,
            &constraints_merge_report,
            expression_interner,
            program_context,
            global_state,
        )?;
        // self.dead_lifetimes.merge(
        //     &other.dead_lifetimes,
        //     heap_merge_report,
        //     constraints,
        //     &constraints_merge_report,
        //     expression_interner,
        //     program_context,
        //     global_state,
        // )?;
        Ok(())
    }

    pub(super) fn leak_check(&self) -> SpannedEncodingResult<()> {
        self.lifetimes.leak_check()?;
        Ok(())
    }

    // pub(super) fn get_dead_lifetime_equality_classes(
    //     &self,
    //     constraints: &BlockConstraints,
    // ) -> SpannedEncodingResult<BTreeMap<String, BTreeSet<String>>> {
    //     self.dead_lifetimes
    //         .get_dead_lifetime_equality_classes(constraints)
    // }

    // pub(super) fn remap_lifetimes(
    //     &mut self,
    //     remaps: BTreeMap<String, String>,
    // ) -> SpannedEncodingResult<()> {
    //     self.dead_lifetimes.remap_lifetimes(remaps)
    // }

    pub(super) fn finalize_block(
        &mut self,
        constraints: &mut BlockConstraints,
    ) -> SpannedEncodingResult<()> {
        self.dead_lifetimes
            .spread_permission_over_eclasses(constraints)
    }
}

#[derive(Default, Clone)]
pub(in super::super) struct HeapAtLabel {
    owned: Owned,
    memory_block: MemoryBlock,
}

impl std::fmt::Display for HeapAtLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", self.owned)?;
        Ok(())
    }
}

enum HeapRef<'a> {
    Current(&'a BlockHeap),
    AtLabel(&'a HeapAtLabel),
}

impl<'a> HeapRef<'a> {
    pub(super) fn find_snapshot(
        &self,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
        heap_variables: &mut HeapVariables,
        constraints: &mut BlockConstraints,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<FindSnapshotResult> {
        match self {
            HeapRef::Current(heap) => match program_context.get_predicate_kind(predicate_name) {
                vir_low::PredicateKind::MemoryBlock => {
                    debug_assert_eq!(predicate_name, MEMORY_BLOCK_PREDICATE_NAME);
                    heap.memory_block.find_snapshot(
                        arguments,
                        heap_variables,
                        constraints,
                        expression_interner,
                        program_context,
                    )
                }
                vir_low::PredicateKind::Owned => heap.owned.find_snapshot(
                    predicate_name,
                    arguments,
                    heap_variables,
                    constraints,
                    expression_interner,
                    program_context,
                ),
                vir_low::PredicateKind::LifetimeToken => todo!(),
                vir_low::PredicateKind::CloseFracRef => todo!(),
                // vir_low::PredicateKind::WithoutSnapshotFrac => todo!(),
                vir_low::PredicateKind::WithoutSnapshotWhole => todo!(),
                vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => todo!(),
                vir_low::PredicateKind::DeadLifetimeToken => todo!(),
                vir_low::PredicateKind::EndBorrowViewShift => todo!(),
            },
            HeapRef::AtLabel(heap) => match program_context.get_predicate_kind(predicate_name) {
                vir_low::PredicateKind::MemoryBlock => {
                    debug_assert_eq!(predicate_name, MEMORY_BLOCK_PREDICATE_NAME);
                    heap.memory_block.find_snapshot(
                        arguments,
                        heap_variables,
                        constraints,
                        expression_interner,
                        program_context,
                    )
                }
                vir_low::PredicateKind::Owned => heap.owned.find_snapshot(
                    predicate_name,
                    arguments,
                    heap_variables,
                    constraints,
                    expression_interner,
                    program_context,
                ),
                vir_low::PredicateKind::LifetimeToken => todo!(),
                vir_low::PredicateKind::CloseFracRef => todo!(),
                // vir_low::PredicateKind::WithoutSnapshotFrac => todo!(),
                vir_low::PredicateKind::WithoutSnapshotWhole => todo!(),
                vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => todo!(),
                vir_low::PredicateKind::DeadLifetimeToken => todo!(),
                vir_low::PredicateKind::EndBorrowViewShift => todo!(),
            },
        }
    }
}
