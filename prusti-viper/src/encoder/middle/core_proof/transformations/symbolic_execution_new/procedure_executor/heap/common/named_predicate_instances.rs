use super::{
    predicate_instance::SnapshotType,
    predicate_instances::{FindSnapshotResult, PermissionType},
    PredicateInstances,
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
                heap::{
                    common::predicate_instance::PredicateInstance,
                    global_heap_state::HeapVariables, utils::matches_arguments, GlobalHeapState,
                    HeapMergeReport,
                },
            },
            program_context::ProgramContext,
        },
    },
};
use prusti_common::config;
use std::collections::BTreeMap;
use vir_crate::{
    common::{display, expression::BinaryOperationHelpers},
    low::{self as vir_low},
};

#[derive(Clone)]
pub(in super::super) struct NamedPredicateInstances<P: PermissionType, S: SnapshotType> {
    predicates: BTreeMap<String, PredicateInstances<P, S>>,
}

impl<P: PermissionType, S: SnapshotType> Default for NamedPredicateInstances<P, S> {
    fn default() -> Self {
        Self {
            predicates: BTreeMap::new(),
        }
    }
}

impl<P: PermissionType, S: std::fmt::Display + SnapshotType> std::fmt::Display
    for NamedPredicateInstances<P, S>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (predicate_name, instances) in &self.predicates {
            write!(f, "{}:\n{}", predicate_name, instances)?;
        }
        Ok(())
    }
}

impl<P: PermissionType> NamedPredicateInstances<P, vir_low::VariableDecl> {
    pub(in super::super) fn find_snapshot(
        &self,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
        heap_variables: &mut HeapVariables,
        constraints: &mut BlockConstraints,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<FindSnapshotResult> {
        if let Some(predicate_instances) = self.predicates.get(predicate_name) {
            predicate_instances.find_snapshot(
                predicate_name,
                arguments,
                heap_variables,
                constraints,
                expression_interner,
                program_context,
            )
        } else {
            Ok(FindSnapshotResult::NotFound)
        }
    }
}

impl<P: PermissionType, S: SnapshotType> NamedPredicateInstances<P, S> {
    pub(in super::super) fn get_instances(
        &self,
        predicate_name: &str,
    ) -> Option<&PredicateInstances<P, S>> {
        self.predicates.get(predicate_name)
    }

    pub(in super::super) fn inhale(
        &mut self,
        program_context: &ProgramContext<impl EncoderContext>,
        expression_interner: &mut ExpressionInterner,
        global_state: &mut GlobalHeapState,
        predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        let predicate_instances = self.predicates.entry(predicate.name.clone()).or_default();
        predicate_instances.inhale(
            program_context,
            expression_interner,
            global_state,
            predicate,
            position,
            constraints,
            block_builder,
        )?;
        Ok(())
    }

    pub(in super::super) fn exhale(
        &mut self,
        program_context: &mut ProgramContext<impl EncoderContext>,
        expression_interner: &mut ExpressionInterner,
        global_state: &mut GlobalHeapState,
        predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        if let Some(predicate_instances) = self.predicates.get_mut(&predicate.name) {
            predicate_instances.exhale(
                program_context,
                expression_interner,
                global_state,
                predicate,
                position,
                constraints,
                block_builder,
            )?;
        } else {
            // Check if non-aliased. If aliased, then emit materialized exhale.
            let is_non_aliased = super::utils::is_non_aliased(
                &predicate.name,
                &predicate.arguments,
                program_context,
                constraints,
            )?;
            block_builder.add_statement(vir_low::Statement::comment(format!(
                "failed to exhale (nothing inhaled): {predicate}"
            )))?;
            if is_non_aliased {
                if config::panic_on_failed_exhale() {
                    panic!("failed to exhale: {predicate}\n{self}");
                }
                block_builder.add_statement(
                    vir_low::Statement::assert_no_pos(false.into()).set_default_position(position),
                )?;
            } else {
                if config::panic_on_failed_exhale()
                    || config::panic_on_failed_exhale_materialization()
                {
                    panic!("failed to exhale: {predicate}\n{self}");
                }
                block_builder.add_statement(vir_low::Statement::exhale(
                    vir_low::Expression::PredicateAccessPredicate(predicate),
                    position,
                ))?;
            }
        }
        Ok(())
    }

    pub(in super::super) fn materialize(
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
        if let Some(predicate_instances) = self.predicates.get_mut(&predicate.name) {
            predicate_instances.materialize(
                program_context,
                expression_interner,
                global_state,
                predicate,
                position,
                constraints,
                block_builder,
                check_that_exists,
            )?;
        } else {
            unimplemented!("TODO: A proper error message");
        }
        Ok(())
    }

    pub(in super::super) fn prepare_for_unhandled_exhale(
        &mut self,
        program_context: &mut ProgramContext<impl EncoderContext>,
        expression_interner: &mut ExpressionInterner,
        global_state: &mut GlobalHeapState,
        predicate_name: &str,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        if let Some(predicate_instances) = self.predicates.get_mut(predicate_name) {
            predicate_instances.prepare_for_unhandled_exhale(
                program_context,
                expression_interner,
                global_state,
                predicate_name,
                position,
                constraints,
                block_builder,
            )?;
        }
        Ok(())
    }

    pub(in super::super) fn merge(
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
        for (predicate_name, self_instances) in &mut self.predicates {
            if let Some(other_instances) = other.predicates.get(predicate_name) {
                self_instances.merge(
                    other_instances,
                    self_edge_block,
                    other_edge_block,
                    predicate_name,
                    position,
                    heap_merge_report,
                    constraints,
                    constraints_merge_report,
                    expression_interner,
                    program_context,
                    global_state,
                )?;
            } else {
                // Nothing to do because we already have the information we need.
                // FIXME: Check whether we need to `PredicateInstance::remap_arguments` here.
            }
        }
        for predicate_name in other.predicates.keys() {
            if !self.predicates.contains_key(predicate_name) {
                // let mut self_predicate_instances = Vec::new();
                // for other_instance in &other.predicates[predicate_name].predicate_instances {
                //     let instance = other_instance.clone();
                //     self_predicate_instances.push(instance);
                // }
                // self.predicates.insert(
                //     predicate_name.clone(),
                //     PredicateInstances::new(self_predicate_instances),
                // );
                self.predicates.insert(
                    predicate_name.clone(),
                    other.predicates[predicate_name].clone(),
                );
                // FIXME: Check whether we need to `PredicateInstance::remap_arguments` here.
            }
        }
        Ok(())
    }
}
