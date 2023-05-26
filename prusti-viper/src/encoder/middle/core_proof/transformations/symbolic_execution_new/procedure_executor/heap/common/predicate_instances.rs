use super::predicate_instance::{PredicateInstance, SnapshotType};
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution::utils::all_heap_independent,
        symbolic_execution_new::{
            block_builder::BlockBuilder,
            egg::ExpressionEGraph,
            expression_interner::ExpressionInterner,
            procedure_executor::{
                constraints::{BlockConstraints, ConstraintsMergeReport},
                heap::{
                    common::utils::MatchesResult,
                    utils::{matches_arguments, matches_arguments_with_remaps},
                    GlobalHeapState, HeapMergeReport,
                },
            },
            program_context::ProgramContext,
        },
    },
};
use prusti_common::config;
use vir_crate::{
    common::{
        display,
        expression::{BinaryOperationHelpers, ExpressionIterator},
    },
    low::{self as vir_low, operations::ty::Typed},
};

pub(in super::super) trait PermissionType: Default + Clone {
    fn inhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()>;
    fn inhale_fresh(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()>;
    fn exhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()>;
}

/// The permission amounts can be either full or none.
#[derive(Default, Clone, Copy)]
pub(in super::super) struct AliasedWholeBool;

/// The permission amounts can be fractional, but we are always guaranteed
/// to operate on the same amount. Therefore, we do not need to perform
/// arithmetic operations on permissions and can use a boolean permission
/// mask with a third parameter that specifies the permission amount that we
/// are currently tracking.
#[derive(Default, Clone, Copy)]
pub(in super::super) struct AliasedFractionalBool;

/// The permission amounts can be fractional and we need to perform
/// arithmetic operations on them. However, the permission amount is bounded
/// by `write` and, therefore, when inhaling `write` we can assume that the
/// current amount is `none`.
#[derive(Default, Clone, Copy)]
pub(in super::super) struct AliasedFractionalBoundedPerm;

/// The permission amounts are natural numbers.
#[derive(Default, Clone, Copy)]
pub(in super::super) struct AliasedWholeNat;

impl PermissionType for AliasedWholeBool {
    fn inhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(
            vir_low::Statement::assert_no_pos(vir_low::Expression::equals(
                permission_variable.clone().into(),
                vir_low::Expression::no_permission(),
            ))
            .set_default_position(position),
        )?;
        self.inhale_fresh(
            permission_variable,
            permission_amount,
            position,
            block_builder,
        )
    }

    fn inhale_fresh(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(
            vir_low::Statement::assign_no_pos(
                permission_variable.clone(),
                permission_amount.clone(),
            )
            .set_default_position(position),
        )?;
        Ok(())
    }

    fn exhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(
            vir_low::Statement::assert_no_pos(vir_low::Expression::equals(
                permission_variable.clone().into(),
                permission_amount.clone(),
            ))
            .set_default_position(position),
        )?;
        block_builder.add_statement(
            vir_low::Statement::assign_no_pos(
                permission_variable.clone(),
                vir_low::Expression::no_permission(),
            )
            .set_default_position(position),
        )?;
        Ok(())
    }
}

impl PermissionType for AliasedFractionalBool {
    fn inhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(
            vir_low::Statement::assert_no_pos(vir_low::Expression::equals(
                permission_variable.clone().into(),
                vir_low::Expression::no_permission(),
            ))
            .set_default_position(position),
        )?;
        self.inhale_fresh(
            permission_variable,
            permission_amount,
            position,
            block_builder,
        )
    }

    fn inhale_fresh(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(
            vir_low::Statement::assign_no_pos(
                permission_variable.clone(),
                permission_amount.clone(),
            )
            .set_default_position(position),
        )?;
        Ok(())
    }

    fn exhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(
            vir_low::Statement::assert_no_pos(vir_low::Expression::equals(
                permission_variable.clone().into(),
                permission_amount.clone(),
            ))
            .set_default_position(position),
        )?;
        block_builder.add_statement(
            vir_low::Statement::assign_no_pos(
                permission_variable.clone(),
                vir_low::Expression::no_permission(),
            )
            .set_default_position(position),
        )?;
        Ok(())
    }
}

impl PermissionType for AliasedFractionalBoundedPerm {
    fn inhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        // FIXME: This is most likely wrong.
        block_builder.add_statement(
            vir_low::Statement::assert_no_pos(vir_low::Expression::equals(
                permission_variable.clone().into(),
                vir_low::Expression::no_permission(),
            ))
            .set_default_position(position),
        )?;
        self.inhale_fresh(
            permission_variable,
            permission_amount,
            position,
            block_builder,
        )
    }

    fn inhale_fresh(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        // FIXME: This is most likely wrong.
        block_builder.add_statement(
            vir_low::Statement::assign_no_pos(
                permission_variable.clone(),
                permission_amount.clone(),
            )
            .set_default_position(position),
        )?;
        Ok(())
    }

    fn exhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        // FIXME: This is most likely wrong.
        block_builder.add_statement(
            vir_low::Statement::assert_no_pos(vir_low::Expression::equals(
                permission_variable.clone().into(),
                permission_amount.clone(),
            ))
            .set_default_position(position),
        )?;
        block_builder.add_statement(
            vir_low::Statement::assign_no_pos(
                permission_variable.clone(),
                vir_low::Expression::no_permission(),
            )
            .set_default_position(position),
        )?;
        Ok(())
    }
}

impl PermissionType for AliasedWholeNat {
    fn inhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(
            vir_low::Statement::assign_no_pos(
                permission_variable.clone(),
                vir_low::Expression::perm_binary_op_no_pos(
                    vir_low::PermBinaryOpKind::Add,
                    permission_variable.clone().into(),
                    permission_amount.clone(),
                ),
            )
            .set_default_position(position),
        )?;
        Ok(())
    }

    fn inhale_fresh(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(
            vir_low::Statement::assign_no_pos(
                permission_variable.clone(),
                permission_amount.clone(),
            )
            .set_default_position(position),
        )?;
        Ok(())
    }

    fn exhale(
        &self,
        permission_variable: &vir_low::VariableDecl,
        permission_amount: &vir_low::Expression,
        position: vir_low::Position,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        block_builder.add_statement(
            vir_low::Statement::assert_no_pos(vir_low::Expression::greater_equals(
                permission_variable.clone().into(),
                permission_amount.clone(),
            ))
            .set_default_position(position),
        )?;
        block_builder.add_statement(
            vir_low::Statement::assign_no_pos(
                permission_variable.clone(),
                vir_low::Expression::perm_binary_op_no_pos(
                    vir_low::PermBinaryOpKind::Sub,
                    permission_variable.clone().into(),
                    permission_amount.clone(),
                ),
            )
            .set_default_position(position),
        )?;
        Ok(())
    }
}

#[derive(Clone)]
pub(in super::super) struct PredicateInstances<P: PermissionType, S: SnapshotType> {
    permission_type: P,
    pub(super) aliased_predicate_instances: Vec<PredicateInstance<S>>,
    pub(super) non_aliased_predicate_instances: Vec<PredicateInstance<S>>,
}

impl<P: PermissionType, S: SnapshotType> Default for PredicateInstances<P, S> {
    fn default() -> Self {
        Self {
            permission_type: Default::default(),
            aliased_predicate_instances: Vec::new(),
            non_aliased_predicate_instances: Vec::new(),
        }
    }
}

impl<P: PermissionType, S: std::fmt::Display + SnapshotType> std::fmt::Display
    for PredicateInstances<P, S>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "  aliased:")?;
        for instance in &self.aliased_predicate_instances {
            writeln!(f, "    {}", instance)?;
        }
        writeln!(f, "  non-aliased:")?;
        for instance in &self.non_aliased_predicate_instances {
            writeln!(f, "    {}", instance)?;
        }
        Ok(())
    }
}

impl<P: PermissionType, S: SnapshotType> PredicateInstances<P, S> {
    pub(in super::super) fn get_aliased_predicate_instances(&self) -> &[PredicateInstance<S>] {
        &self.aliased_predicate_instances
    }

    fn is_non_aliased_predicate(
        &self,
        predicate: &vir_low::PredicateAccessPredicate,
        program_context: &ProgramContext<impl EncoderContext>,
        constraints: &mut BlockConstraints,
    ) -> SpannedEncodingResult<bool> {
        super::utils::is_non_aliased(
            &predicate.name,
            &predicate.arguments,
            program_context,
            constraints,
        )
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
        assert!(
            all_heap_independent(&predicate.arguments),
            "arguments: {}",
            display::cjoin(&predicate.arguments)
        );
        let is_non_aliased =
            self.is_non_aliased_predicate(&predicate, program_context, constraints)?;
        if is_non_aliased {
            for predicate_instance in &mut self.non_aliased_predicate_instances {
                let result = super::utils::predicate_matches_non_aliased(
                    &predicate,
                    &predicate_instance.arguments,
                    expression_interner,
                    program_context,
                    constraints,
                )?;
                match &result {
                    MatchesResult::MatchesConditionally { .. }
                    | MatchesResult::MatchesUnonditionally => {
                        if let MatchesResult::MatchesConditionally { assert } = result {
                            block_builder.add_statement(
                                vir_low::Statement::assert_no_pos(assert)
                                    .set_default_position(position),
                            )?;
                        }
                        // Predicate instance already exists, but should be with no permission.
                        assert_eq!(predicate_instance.permission_amount, *predicate.permission);
                        assert!(
                            !predicate_instance.is_materialized,
                            "non-aliased predicates should never be materialized"
                        );
                        self.permission_type.inhale(
                            &predicate_instance.permission_variable,
                            &predicate.permission,
                            position,
                            block_builder,
                        )?;
                        return Ok(());
                    }
                    MatchesResult::DoesNotMatch => {}
                }
            }
        } else {
            for predicate_instance in &mut self.aliased_predicate_instances {
                if matches_arguments(
                    &predicate_instance.arguments,
                    &predicate.arguments,
                    constraints,
                    expression_interner,
                    program_context,
                )? {
                    // Predicate instance already exists, but should be with no permission.
                    assert_eq!(predicate_instance.permission_amount, *predicate.permission);
                    if predicate_instance.is_materialized {
                        // Predicate instance is materialized, so we should keep the
                        // inhale.
                        block_builder.add_statement(
                            vir_low::Statement::inhale_no_pos(
                                vir_low::Expression::PredicateAccessPredicate(predicate),
                            )
                            .set_default_position(position),
                        )?;
                    } else {
                        self.permission_type.inhale(
                            &predicate_instance.permission_variable,
                            &predicate.permission,
                            position,
                            block_builder,
                        )?;
                    }
                    return Ok(());
                }
            }
        }
        // Predicate instance does not exist, create a new one.
        let snapshot_variable = <S as SnapshotType>::create_snapshot_variable(
            &predicate.name,
            program_context,
            global_state,
        )?;
        let permission_variable = global_state.create_permission_variable(&predicate.name);
        self.permission_type.inhale_fresh(
            &permission_variable,
            &predicate.permission,
            position,
            block_builder,
        )?;
        let predicate_instance = PredicateInstance {
            arguments: predicate.arguments,
            snapshot_variable,
            permission_amount: *predicate.permission,
            permission_variable,
            is_materialized: false,
            is_unconditional: true,
        };
        if is_non_aliased {
            self.non_aliased_predicate_instances
                .push(predicate_instance);
        } else {
            self.aliased_predicate_instances.push(predicate_instance);
        }
        Ok(())
    }

    pub(in super::super) fn exhale(
        &mut self,
        program_context: &mut ProgramContext<impl EncoderContext>,
        expression_interner: &mut ExpressionInterner,
        _global_state: &mut GlobalHeapState,
        predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        assert!(
            all_heap_independent(&predicate.arguments),
            "arguments: {}",
            display::cjoin(&predicate.arguments)
        );
        let is_non_aliased =
            self.is_non_aliased_predicate(&predicate, program_context, constraints)?;
        let position = {
            let current_error_context = program_context.env().get_error_context(position);
            let new_error_context = match current_error_context {
                ErrorCtxt::ProcedureCall => ErrorCtxt::ProcedureCallPermissionExhale,
                ErrorCtxt::DropCall => ErrorCtxt::DropCallPermissionExhale,
                ErrorCtxt::ExhaleMethodPrecondition => {
                    ErrorCtxt::ExhaleMethodPreconditionPermissionExhale
                }
                ErrorCtxt::ExhaleMethodPostcondition => {
                    ErrorCtxt::ExhaleMethodPostconditionPermissionExhale
                }
                ErrorCtxt::AssertMethodPostcondition => {
                    ErrorCtxt::AssertMethodPostconditionPermissionExhale
                }
                _ => current_error_context,
            };
            program_context
                .env()
                .change_error_context(position, new_error_context)
        };
        if is_non_aliased {
            for (i, predicate_instance) in
                self.non_aliased_predicate_instances.iter_mut().enumerate()
            {
                let result = super::utils::predicate_matches_non_aliased(
                    &predicate,
                    &predicate_instance.arguments,
                    expression_interner,
                    program_context,
                    constraints,
                )?;
                match &result {
                    MatchesResult::MatchesConditionally { .. }
                    | MatchesResult::MatchesUnonditionally => {
                        if let MatchesResult::MatchesConditionally { assert } = result {
                            block_builder.add_statement(
                                vir_low::Statement::assert_no_pos(assert)
                                    .set_default_position(position),
                            )?;
                        }
                        let predicate_instance = self.non_aliased_predicate_instances.remove(i);
                        assert_eq!(predicate_instance.permission_amount, *predicate.permission);
                        assert!(
                            !predicate_instance.is_materialized,
                            "non-aliased predicates should never be materialized"
                        );
                        self.permission_type.exhale(
                            &predicate_instance.permission_variable,
                            &predicate.permission,
                            position,
                            block_builder,
                        )?;
                        return Ok(());
                    }
                    MatchesResult::DoesNotMatch => {}
                }
            }
            if config::panic_on_failed_exhale() {
                panic!("failed to exhale: {predicate}\n{self}");
            } else {
                block_builder.add_statement(vir_low::Statement::comment(format!(
                    "failed to exhale: {predicate}"
                )))?;
                block_builder.add_statement(
                    vir_low::Statement::assert_no_pos(false.into()).set_default_position(position),
                )?;
                constraints.assume_false()?;
            }
        } else {
            constraints.saturate_solver()?;
            for (i, predicate_instance) in self.aliased_predicate_instances.iter().enumerate() {
                if matches_arguments(
                    &predicate_instance.arguments,
                    &predicate.arguments,
                    constraints,
                    expression_interner,
                    program_context,
                )? {
                    if (predicate_instance.is_unconditional
                        || config::ignore_whether_exhale_is_unconditional())
                        || predicate_instance.is_materialized
                        || self.aliased_predicate_instances.len() == 1
                    {
                        let predicate_instance = self.aliased_predicate_instances.remove(i);
                        assert_eq!(predicate_instance.permission_amount, *predicate.permission);
                        if predicate_instance.is_materialized {
                            // The predicate instance is materialized, so we need to
                            // produce a materialized exhale.
                            block_builder.add_statement(
                                vir_low::Statement::exhale_no_pos(
                                    vir_low::Expression::PredicateAccessPredicate(predicate),
                                )
                                .set_default_position(position),
                            )?;
                            return Ok(());
                        } else {
                            self.permission_type.exhale(
                                &predicate_instance.permission_variable,
                                &predicate.permission,
                                position,
                                block_builder,
                            )?;
                        }
                        return Ok(());
                    } else {
                        // The predicate instance is conditional, so we need to
                        // materialize the exhale.
                        break;
                    }
                }
            }
            if config::panic_on_failed_exhale() || config::panic_on_failed_exhale_materialization()
            {
                panic!("failed to exhale: {predicate}\n{self}");
            } else {
                block_builder.add_statement(vir_low::Statement::comment(format!(
                    "failed to exhale: {predicate}"
                )))?;
                self.materialize_aliased_instances(
                    &predicate.name,
                    position,
                    constraints,
                    block_builder,
                    program_context,
                )?;
                block_builder.add_statement(vir_low::Statement::exhale(
                    vir_low::Expression::PredicateAccessPredicate(predicate),
                    position,
                ))?;
            }
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
        self.materialize_aliased_instances(
            predicate_name,
            position,
            constraints,
            block_builder,
            program_context,
        )?;
        Ok(())
    }

    pub(in super::super) fn find_snapshot(
        &self,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
        constraints: &mut BlockConstraints,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<Option<(S, Option<vir_low::Expression>)>> {
        assert!(
            all_heap_independent(arguments),
            "arguments: {}",
            display::cjoin(arguments)
        );
        for predicate_instance in &self.non_aliased_predicate_instances {
            match super::utils::matches_non_aliased(
                predicate_name,
                arguments,
                &predicate_instance.arguments,
                expression_interner,
                program_context,
                constraints,
            )? {
                MatchesResult::MatchesConditionally { assert } => {
                    return Ok(Some((
                        predicate_instance.snapshot_variable.clone(),
                        Some(assert),
                    )));
                }
                MatchesResult::MatchesUnonditionally => {
                    return Ok(Some((predicate_instance.snapshot_variable.clone(), None)));
                }
                MatchesResult::DoesNotMatch => {} // return Ok(Some(predicate_instance.snapshot_variable.clone()));
            }
        }
        for predicate_instance in &self.aliased_predicate_instances {
            if matches_arguments(
                &predicate_instance.arguments,
                arguments,
                constraints,
                expression_interner,
                program_context,
            )? {
                return Ok(Some((predicate_instance.snapshot_variable.clone(), None)));
            }
        }
        Ok(None)
    }

    pub(in super::super) fn merge(
        &mut self,
        other: &Self,
        self_edge_block: &mut Vec<vir_low::Statement>,
        other_edge_block: &mut Vec<vir_low::Statement>,
        predicate_name: &str,
        position: vir_low::Position,
        heap_merge_report: &mut HeapMergeReport,
        constraints: &mut BlockConstraints,
        constraints_merge_report: &ConstraintsMergeReport,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        self.merge_non_aliased(
            other,
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
        self.merge_aliased(
            other,
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
        Ok(())
    }

    fn merge_non_aliased(
        &mut self,
        other: &Self,
        self_edge_block: &mut Vec<vir_low::Statement>,
        other_edge_block: &mut Vec<vir_low::Statement>,
        predicate_name: &str,
        position: vir_low::Position,
        heap_merge_report: &mut HeapMergeReport,
        constraints: &mut BlockConstraints,
        constraints_merge_report: &ConstraintsMergeReport,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        let mut other_used = vec![false; other.non_aliased_predicate_instances.len()];
        for self_instance in &mut self.non_aliased_predicate_instances {
            self_instance.remap_arguments(constraints_merge_report.get_self_remaps())?;
            let mut found = false;
            for (i, other_instance) in other.non_aliased_predicate_instances.iter().enumerate() {
                let (are_equal, disequalities) = super::utils::matches_non_aliased_diff(
                    predicate_name,
                    &self_instance.arguments,
                    &other_instance.arguments,
                    expression_interner,
                    program_context,
                    constraints,
                )?;
                if are_equal {
                    for (self_arg, other_arg) in disequalities {
                        let variable =
                            global_state.create_merge_variable(self_arg.get_type().clone());
                        self_edge_block.push(
                            vir_low::Statement::assume_no_pos(vir_low::Expression::equals(
                                variable.clone().into(),
                                self_arg,
                            ))
                            .set_default_position(position),
                        );
                        other_edge_block.push(
                            vir_low::Statement::assume_no_pos(vir_low::Expression::equals(
                                variable.clone().into(),
                                other_arg,
                            ))
                            .set_default_position(position),
                        );
                    }
                    assert!(!other_used[i]);
                    other_used[i] = true;
                    self_instance.merge(
                        other_instance,
                        self_edge_block,
                        other_edge_block,
                        predicate_name,
                        position,
                        heap_merge_report,
                        constraints,
                        expression_interner,
                        program_context,
                        global_state,
                    )?;
                    found = true;
                    break;
                }
            }
            if !found {
                // The permission amount is tracked by the verifier, so we do
                // not need to do anything.
            }
        }
        for (i, used) in other_used.iter().enumerate() {
            if !*used {
                let instance = other.non_aliased_predicate_instances[i].clone();
                self.non_aliased_predicate_instances.push(instance);
            }
        }
        Ok(())
    }

    fn merge_aliased(
        &mut self,
        other: &Self,
        self_edge_block: &mut Vec<vir_low::Statement>,
        other_edge_block: &mut Vec<vir_low::Statement>,
        predicate_name: &str,
        position: vir_low::Position,
        heap_merge_report: &mut HeapMergeReport,
        constraints: &mut BlockConstraints,
        constraints_merge_report: &ConstraintsMergeReport,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        let mut other_used = vec![false; other.aliased_predicate_instances.len()];
        let mut needs_state_consolidation = false;
        for self_instance in &mut self.aliased_predicate_instances {
            self_instance.remap_arguments(constraints_merge_report.get_self_remaps())?;
            let mut found = false;
            for (i, other_instance) in other.aliased_predicate_instances.iter().enumerate() {
                if matches_arguments(
                    &self_instance.arguments,
                    &other_instance.arguments,
                    constraints,
                    expression_interner,
                    program_context,
                )? || matches_arguments_with_remaps(
                    &self_instance.arguments,
                    &other_instance.arguments,
                    constraints_merge_report,
                    constraints,
                    expression_interner,
                    program_context,
                )? {
                    if other_used[i] {
                        // We have two elements in self that are equal to `i`th
                        // in other. This means that they are equal to each
                        // other and we can merge them.
                        needs_state_consolidation = true;
                    }
                    other_used[i] = true;
                    self_instance.merge(
                        other_instance,
                        self_edge_block,
                        other_edge_block,
                        predicate_name,
                        position,
                        heap_merge_report,
                        constraints,
                        expression_interner,
                        program_context,
                        global_state,
                    )?;
                    found = true;
                    break;
                }
            }
            if !found {
                // The permission amount is tracked by the verifier, so we only
                // need to mark that the instance is conditional.
                self_instance.is_unconditional = false;
            }
        }
        for (i, used) in other_used.iter().enumerate() {
            if !*used {
                let mut instance = other.aliased_predicate_instances[i].clone();
                instance.is_unconditional = false;
                self.aliased_predicate_instances.push(instance);
                // This could mean that we have two elements in other that are
                // equal to each other and, therefore, we may need to merge
                // them.
                needs_state_consolidation = true;
            }
        }
        if needs_state_consolidation {
            self.consolidate_state(
                self_edge_block,
                predicate_name,
                position,
                heap_merge_report,
                constraints,
                expression_interner,
                program_context,
                global_state,
            )?;
        }
        Ok(())
    }

    fn consolidate_state(
        &mut self,
        self_edge_block: &mut Vec<vir_low::Statement>,
        predicate_name: &str,
        position: vir_low::Position,
        heap_merge_report: &mut HeapMergeReport,
        constraints: &mut BlockConstraints,
        expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        let mut matching_instances = Vec::new();
        for (i, first_instance) in self.aliased_predicate_instances.iter().enumerate() {
            for (j, second_instance) in self
                .aliased_predicate_instances
                .iter()
                .enumerate()
                .skip(i + 1)
            {
                if matches_arguments(
                    &first_instance.arguments,
                    &second_instance.arguments,
                    constraints,
                    expression_interner,
                    program_context,
                )? {
                    matching_instances.push((i, j));
                }
            }
        }
        let mut other_edge_block = Vec::new();
        let mut first_invalid_index = self.aliased_predicate_instances.len();
        for (i, j) in matching_instances.into_iter().rev() {
            assert!(i < j);
            assert!(j < first_invalid_index);
            let second_instance = self.aliased_predicate_instances.remove(j);
            first_invalid_index = j;
            let first_instance = self.aliased_predicate_instances.get_mut(i).unwrap();
            first_instance.merge(
                &second_instance,
                self_edge_block,
                &mut other_edge_block,
                predicate_name,
                position,
                heap_merge_report,
                constraints,
                expression_interner,
                program_context,
                global_state,
            )?;
        }
        self_edge_block.extend(other_edge_block);
        Ok(())
    }

    fn materialize_aliased_instances(
        &mut self,
        predicate_name: &str,
        position: vir_low::Position,
        constraints: &mut BlockConstraints,
        block_builder: &mut BlockBuilder,
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<()> {
        let mut statements = vec![vir_low::Statement::comment(
            "Materializing predicates".to_string(),
        )];
        for instance in &mut self.aliased_predicate_instances {
            if !super::utils::is_non_aliased(
                predicate_name,
                &instance.arguments,
                program_context,
                constraints,
            )? && !instance.is_materialized
            {
                instance.is_materialized = true;
                let statement = instance.create_materialization_statement(
                    predicate_name,
                    position,
                    program_context,
                )?;
                statements.push(statement);
            }
        }
        block_builder.add_statements_at_materialization_point(statements)?;
        // self.predicate_instances
        //     .retain(|instance| !instance.is_materialized);
        Ok(())
    }
}
