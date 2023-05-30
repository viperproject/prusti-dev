use super::{
    common::{AliasedFractionalBool, FindSnapshotResult, NamedPredicateInstances},
    global_heap_state::HeapVariables,
    merge_report::HeapMergeReport,
    GlobalHeapState,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution::utils::all_heap_independent,
        symbolic_execution_new::{
            block_builder::BlockBuilder,
            expression_interner::ExpressionInterner,
            procedure_executor::{
                constraints::{BlockConstraints, ConstraintsMergeReport},
                heap::utils::matches_arguments,
            },
            program_context::ProgramContext,
        },
    },
};
use std::collections::BTreeMap;
use vir_crate::{
    common::{display, expression::BinaryOperationHelpers},
    low::{self as vir_low},
};

#[derive(Default, Clone)]
pub(super) struct Owned {
    predicates: NamedPredicateInstances<AliasedFractionalBool, vir_low::VariableDecl>,
}

impl std::fmt::Display for Owned {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.predicates)
    }
}

impl Owned {
    pub(super) fn inhale(
        &mut self,
        program_context: &ProgramContext<impl EncoderContext>,
        expression_interner: &mut ExpressionInterner,
        global_state: &mut GlobalHeapState,
        predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        self.predicates.inhale(
            program_context,
            expression_interner,
            global_state,
            predicate,
            position,
            constraints,
            block_builder,
        )
    }

    pub(super) fn exhale(
        &mut self,
        program_context: &mut ProgramContext<impl EncoderContext>,
        expression_interner: &mut ExpressionInterner,
        global_state: &mut GlobalHeapState,
        predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        self.predicates.exhale(
            program_context,
            expression_interner,
            global_state,
            predicate,
            position,
            constraints,
            block_builder,
        )
    }

    pub(super) fn materialize(
        &mut self,
        program_context: &mut ProgramContext<impl EncoderContext>,
        expression_interner: &mut ExpressionInterner,
        global_state: &mut GlobalHeapState,
        predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
        check_that_exists: bool,
    ) -> SpannedEncodingResult<()> {
        self.predicates.materialize(
            program_context,
            expression_interner,
            global_state,
            predicate,
            position,
            constraints,
            block_builder,
            check_that_exists,
        )
    }

    pub(super) fn prepare_for_unhandled_exhale(
        &mut self,
        program_context: &mut ProgramContext<impl EncoderContext>,
        expression_interner: &mut ExpressionInterner,
        global_state: &mut GlobalHeapState,
        predicate_name: &str,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        self.predicates.prepare_for_unhandled_exhale(
            program_context,
            expression_interner,
            global_state,
            predicate_name,
            position,
            constraints,
            block_builder,
        )
    }

    pub(super) fn find_snapshot(
        &self,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
        global_state: &mut HeapVariables,
        constraints: &mut BlockConstraints,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<FindSnapshotResult> {
        self.predicates.find_snapshot(
            predicate_name,
            arguments,
            global_state,
            constraints,
            expression_interner,
            program_context,
        )
    }

    pub(super) fn merge(
        &mut self,
        other: &Self,
        self_edge_block: &mut Vec<vir_low::Statement>,
        other_edge_block: &mut Vec<vir_low::Statement>,
        position: vir_low::Position,
        heap_merge_report: &mut HeapMergeReport,
        constraints: &mut BlockConstraints,
        constraints_merge_report: &ConstraintsMergeReport,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        self.predicates.merge(
            &other.predicates,
            self_edge_block,
            other_edge_block,
            position,
            heap_merge_report,
            constraints,
            constraints_merge_report,
            expression_interner,
            program_context,
            global_state,
        )
    }
}
