use super::{
    common::{AliasedFractionalBool, AliasedWholeBool, NamedPredicateInstances, NoSnapshot},
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
pub(super) struct ClosedFracRef {
    predicates: NamedPredicateInstances<AliasedWholeBool, NoSnapshot>,
}

impl std::fmt::Display for ClosedFracRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.predicates)
    }
}

impl ClosedFracRef {
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
        self.try_assert_frac_ref_snapshot_equality(
            program_context,
            expression_interner,
            &predicate,
            position,
            constraints,
            block_builder,
        )?;
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

    fn try_assert_frac_ref_snapshot_equality(
        &mut self,
        program_context: &mut ProgramContext<impl EncoderContext>,
        expression_interner: &mut ExpressionInterner,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        if let Some(predicate_instances) = self.predicates.get_instances(&predicate.name) {
            let predicate_lifetime = &predicate.arguments[0];
            let predicate_snapshot = &predicate.arguments[4];
            let mut snapshot_candidate = None;
            for predicate_instance in predicate_instances.get_aliased_predicate_instances() {
                let instance_lifetime = predicate_instance.get_argument(0);
                if constraints.is_equal(
                    expression_interner,
                    program_context,
                    predicate_lifetime,
                    instance_lifetime,
                )? {
                    if snapshot_candidate.is_some() {
                        // There are multiple snapshots for the same lifetime.
                        // We cannot assert anything.
                        return Ok(());
                    }
                    snapshot_candidate = Some(predicate_instance.get_argument(4));
                }
            }
            if let Some(instance_snapshot) = snapshot_candidate {
                block_builder.add_statement(vir_low::Statement::comment(format!(
                    "Asserting that the snapshot of {} is equal to the snapshot of the predicate instance",
                    predicate.name
                )))?;
                // This does not work because we do not have accees to the lowerer
                // anymore ☹.
                //
                // ```rust
                // let extensionality_trigger =
                //     self.lowerer.snapshots_extensionality_equal_call(
                //     predicate_snapshot.clone(), instance_snapshot.clone(),
                //     position, )?;
                // ```
                //
                // Instead, we use the following hack.
                let extensionality_trigger = program_context
                    .predicate_snapshots_extensionality_call(
                        predicate_snapshot.clone(),
                        instance_snapshot.clone(),
                        position,
                    );
                block_builder
                    .add_statement(vir_low::Statement::assert(extensionality_trigger, position))?;
            }
        }
        Ok(())
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
