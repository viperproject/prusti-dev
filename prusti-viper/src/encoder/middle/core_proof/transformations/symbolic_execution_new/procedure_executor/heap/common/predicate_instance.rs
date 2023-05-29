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
                    global_heap_state::HeapVariables, utils::matches_arguments, GlobalHeapState,
                    HeapMergeReport,
                },
            },
            program_context::ProgramContext,
        },
    },
};
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use vir_crate::{
    common::{
        display,
        expression::{BinaryOperationHelpers, ExpressionIterator},
    },
    low::{self as vir_low},
};

pub(in super::super) trait SnapshotType: Clone + std::fmt::Display {
    fn merge_snapshots(
        &mut self,
        other: &Self,
        predicate_name: &str,
        heap_merge_report: &mut HeapMergeReport,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()>;
    fn create_snapshot_variable(
        predicate_name: &str,
        program_context: &ProgramContext<impl EncoderContext>,
        heap_variables: &mut HeapVariables,
    ) -> SpannedEncodingResult<Self>;
    fn as_expression(&self) -> Option<vir_low::Expression>;
}

#[derive(Clone, Debug, Default)]
pub(in super::super) struct NoSnapshot;

impl std::fmt::Display for NoSnapshot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NoSnapshot")
    }
}

#[derive(Clone)]
pub(in super::super) struct PredicateInstance<S: SnapshotType> {
    /// Arguments of the predicate instance.
    pub(super) arguments: Vec<vir_low::Expression>,
    /// Snapshot of the predicate instance.
    pub(super) snapshot_variable: S,
    /// The permission amount of the predicate instance.
    pub(super) permission_amount: vir_low::Expression,
    /// The variable that holds the permission amount. The value of the variable
    /// should be equal to `permission_amount` unless we are in a trace in which
    /// the predciate was not inhaled.
    pub(super) permission_variable: vir_low::VariableDecl,
    /// Whether the predicate inhale was emitted as a Viper statement or is the
    /// state tracked only in the symbolic execution.
    ///
    /// We use this flag instead of just forgetting the chunk because of the
    /// following example:
    ///
    /// ```viper
    /// inhale R
    /// if cond {
    ///     exhale R2 // an exhale that triggers materialization
    /// }
    /// exhale R
    /// ```
    ///
    /// If we forgot about `R` at the materialization point, we would not be
    /// able to verify `exhale R`: since we would still have a chunk with `R`
    /// from the else branch, we would try to use its permission, but that would
    /// inevitably fail.
    pub(super) is_materialized: bool,
    /// Is this predicate instance present on all incoming traces or just some
    /// of them?
    pub(super) is_unconditional: bool,
}

impl SnapshotType for vir_low::VariableDecl {
    fn merge_snapshots(
        &mut self,
        other: &Self,
        predicate_name: &str,
        heap_merge_report: &mut HeapMergeReport,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        if self != other {
            *self = heap_merge_report.remap_snapshot_variable(
                predicate_name,
                self,
                other,
                global_state,
            );
        }
        Ok(())
    }

    fn create_snapshot_variable(
        predicate_name: &str,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut HeapVariables,
    ) -> SpannedEncodingResult<Self> {
        let Some(ty) = program_context.get_snapshot_type(predicate_name) else {
            unreachable!();
        };
        Ok(global_state.create_snapshot_variable(predicate_name, ty))
    }

    fn as_expression(&self) -> Option<vir_low::Expression> {
        Some(self.clone().into())
    }
}

impl SnapshotType for NoSnapshot {
    fn merge_snapshots(
        &mut self,
        _other: &Self,
        _predicate_name: &str,
        _heap_merge_report: &mut HeapMergeReport,
        _global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        Ok(())
    }

    fn create_snapshot_variable(
        _predicate_name: &str,
        _program_context: &ProgramContext<impl EncoderContext>,
        _global_state: &mut HeapVariables,
    ) -> SpannedEncodingResult<Self> {
        Ok(NoSnapshot)
    }

    fn as_expression(&self) -> Option<vir_low::Expression> {
        None
    }
}

impl<S: SnapshotType> PredicateInstance<S> {
    pub(in super::super) fn get_argument(&self, index: usize) -> &vir_low::Expression {
        &self.arguments[index]
    }

    pub(super) fn remap_arguments(
        &mut self,
        remaps: &FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>,
    ) -> SpannedEncodingResult<()> {
        for argument in std::mem::take(&mut self.arguments) {
            let remapped_argument = argument.map_variables(|variable| {
                if let Some(remap) = remaps.get(&variable) {
                    remap.clone()
                } else {
                    variable
                }
            });
            self.arguments.push(remapped_argument);
        }
        Ok(())
    }

    pub(super) fn merge(
        &mut self,
        other: &Self,
        self_edge_block: &mut Vec<vir_low::Statement>,
        other_edge_block: &mut Vec<vir_low::Statement>,
        predicate_name: &str,
        position: vir_low::Position,
        heap_merge_report: &mut HeapMergeReport,
        _constraints: &BlockConstraints,
        _expression_interner: &mut ExpressionInterner,
        program_context: &ProgramContext<impl EncoderContext>,
        global_state: &mut GlobalHeapState,
    ) -> SpannedEncodingResult<()> {
        assert_eq!(self.arguments.len(), other.arguments.len());
        if self.is_materialized != other.is_materialized {
            if !self.is_materialized {
                self_edge_block.push(self.create_materialization_statement(
                    predicate_name,
                    position,
                    program_context,
                )?);
            }
            if !other.is_materialized {
                other_edge_block.push(other.create_materialization_statement(
                    predicate_name,
                    position,
                    program_context,
                )?);
            }
            self.is_materialized = true;
        }
        if self.is_unconditional != other.is_unconditional {
            self.is_unconditional = false;
        }
        assert_eq!(self.permission_amount, other.permission_amount);
        self.snapshot_variable.merge_snapshots(
            &other.snapshot_variable,
            predicate_name,
            heap_merge_report,
            global_state,
        )?;
        if self.permission_variable != other.permission_variable {
            self.permission_variable = heap_merge_report.remap_permission_variable(
                predicate_name,
                &self.permission_variable,
                &other.permission_variable,
                global_state,
            );
        }
        Ok(())
    }

    pub(super) fn create_materialization_statement(
        &self,
        predicate_name: &str,
        position: vir_low::Position,
        program_context: &ProgramContext<impl EncoderContext>,
    ) -> SpannedEncodingResult<vir_low::Statement> {
        use vir_low::macros::*;
        let permission = vir_low::Expression::predicate_access_predicate_no_pos(
            predicate_name.to_string(),
            self.arguments.clone(),
            self.permission_variable.clone().into(),
        );
        let snapshot = if let Some(snapshot) = self.snapshot_variable.as_expression() {
            let function_name = program_context.get_predicate_snapshot_function(predicate_name);
            let snapshot_type = program_context.get_snapshot_type(predicate_name).unwrap();
            let snapshot_equality = vir_low::Expression::equals(
                snapshot,
                vir_low::Expression::function_call(
                    function_name,
                    self.arguments.clone(),
                    snapshot_type,
                ),
            );
            expr! {
                ([self.permission_variable.clone().into()] !=
                    [vir_low::Expression::no_permission()]) ==>
                [snapshot_equality]
            }
        } else {
            true.into()
        };
        let statement =
            vir_low::Statement::inhale_no_pos(vir_low::Expression::and(permission, snapshot))
                .set_default_position(position);
        Ok(statement)
    }

    pub(super) fn create_matches_check(
        &self,
        predicate_arguments: &[vir_low::Expression],
        predicate_permission: &vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let guard = self
            .arguments
            .iter()
            .zip(predicate_arguments.iter())
            .map(|(instance_argument, predicate_argument)| {
                vir_low::Expression::equals(instance_argument.clone(), predicate_argument.clone())
            })
            .chain(std::iter::once(vir_low::Expression::equals(
                self.permission_variable.clone().into(),
                (*predicate_permission).clone(),
            )))
            .conjoin();
        Ok(guard)
    }
}

impl<S: std::fmt::Display + SnapshotType> std::fmt::Display for PredicateInstance<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}; {}: {} {}",
            display::cjoin(&self.arguments),
            self.permission_amount,
            self.snapshot_variable,
            self.permission_variable,
        )?;
        if self.is_materialized {
            write!(f, " materialized")?;
        }
        if self.is_unconditional {
            write!(f, " unconditional")?;
        }
        Ok(())
    }
}
