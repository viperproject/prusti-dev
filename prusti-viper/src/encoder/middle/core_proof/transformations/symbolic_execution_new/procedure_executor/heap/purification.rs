use super::{
    common::FindSnapshotResult, global_heap_state::HeapVariables, BlockHeap, GlobalHeapState,
    HeapAtLabel, HeapRef,
};
use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    middle::core_proof::{
        transformations::{
            encoder_context::EncoderContext,
            symbolic_execution_new::{
                expression_interner::ExpressionInterner,
                procedure_executor::constraints::BlockConstraints, program_context::ProgramContext,
            },
        },
        utils::bound_variable_stack::{BoundVariableStack, BoundVariableStackLow},
    },
};
use std::collections::BTreeMap;
use vir_crate::{
    common::{
        expression::{BinaryOperationHelpers, ExpressionIterator, UnaryOperationHelpers},
        position::Positioned,
    },
    low::{self as vir_low, expression::visitors::ExpressionFallibleFolder},
};

pub(in super::super) struct SnapshotBinding {
    /// Under which condition this binding gets activated.
    pub(in super::super) guard: vir_low::Expression,
    /// A fresh variable to which the snapshot is bound.
    pub(in super::super) variable: vir_low::VariableDecl,
    pub(in super::super) guarded_candidates: Vec<(vir_low::Expression, vir_low::VariableDecl)>,
}

pub(in super::super) struct PurificationResult {
    pub(in super::super) expression: vir_low::Expression,
    pub(in super::super) guarded_assertions: Vec<vir_low::Expression>,
    pub(in super::super) bindings: Vec<SnapshotBinding>,
}

pub(in super::super) fn purify_snap_function_calls(
    heap: &BlockHeap,
    global_heap_state: &mut GlobalHeapState,
    program_context: &ProgramContext<impl EncoderContext>,
    constraints: &mut BlockConstraints,
    expression_interner: &mut ExpressionInterner,
    expression: vir_low::Expression,
) -> SpannedEncodingResult<PurificationResult> {
    let mut purifier = Purifier {
        predicate_snapshots: heap,
        predicate_snapshots_at_label: &global_heap_state.snapshots_at_label,
        heap_variables: &mut global_heap_state.heap_variables,
        constraints,
        expression_interner,
        program_context,
        path_condition: Vec::new(),
        guarded_assertions: Vec::new(),
        bindings: Vec::new(),
        bound_variables: Default::default(),
        label: None,
    };
    let mut expression = purifier.fallible_fold_expression(expression)?;
    assert!(purifier.path_condition.is_empty());
    if !expression.is_heap_independent() {
        purifier.constraints.saturate_solver()?;
        expression = purifier.fallible_fold_expression(expression)?;
    }
    assert!(purifier.path_condition.is_empty());
    Ok(PurificationResult {
        expression,
        guarded_assertions: purifier.guarded_assertions,
        bindings: purifier.bindings,
    })
}

struct Purifier<'a, EC: EncoderContext> {
    predicate_snapshots: &'a BlockHeap,
    predicate_snapshots_at_label: &'a BTreeMap<String, HeapAtLabel>,
    heap_variables: &'a mut HeapVariables,
    constraints: &'a mut BlockConstraints,
    expression_interner: &'a mut ExpressionInterner,
    program_context: &'a ProgramContext<'a, EC>,
    path_condition: Vec<vir_low::Expression>,
    guarded_assertions: Vec<vir_low::Expression>,
    bindings: Vec<SnapshotBinding>,
    bound_variables: BoundVariableStack,
    label: Option<String>,
}

impl<'a, EC: EncoderContext> ExpressionFallibleFolder for Purifier<'a, EC> {
    type Error = SpannedEncodingError;

    fn fallible_fold_trigger(
        &mut self,
        mut trigger: vir_low::Trigger,
    ) -> Result<vir_low::Trigger, Self::Error> {
        for term in std::mem::take(&mut trigger.terms) {
            let new_term = self.fallible_fold_expression(term)?;
            trigger.terms.push(new_term);
        }
        Ok(trigger)
    }

    fn fallible_fold_func_app_enum(
        &mut self,
        func_app: vir_low::expression::FuncApp,
    ) -> Result<vir_low::Expression, Self::Error> {
        let func_app = self.fallible_fold_func_app(func_app)?;
        let function = self.program_context.get_function(&func_app.function_name);
        assert_eq!(function.parameters.len(), func_app.arguments.len());
        match function.kind {
            vir_low::FunctionKind::CallerFor | vir_low::FunctionKind::SnapRange => {
                Ok(vir_low::Expression::FuncApp(func_app))
            }
            vir_low::FunctionKind::MemoryBlockBytes | vir_low::FunctionKind::Snap => {
                match self.resolve_snapshot(&func_app.function_name, &func_app.arguments)? {
                    FindSnapshotResult::NotFound => Ok(vir_low::Expression::FuncApp(func_app)),
                    FindSnapshotResult::FoundGuarded {
                        snapshot,
                        precondition,
                    } => {
                        if let Some(assertion) = precondition {
                            let guarded_assertion = vir_low::Expression::implies(
                                self.path_condition.clone().into_iter().conjoin(),
                                assertion,
                            );
                            self.guarded_assertions.push(guarded_assertion);
                        }
                        Ok(vir_low::Expression::local(snapshot, func_app.position))
                    }
                    FindSnapshotResult::FoundConditional {
                        binding,
                        guarded_candidates,
                    } => {
                        self.bindings.push(SnapshotBinding {
                            guard: self.path_condition.clone().into_iter().conjoin(),
                            variable: binding.clone(),
                            guarded_candidates,
                        });
                        Ok(vir_low::Expression::local(binding, func_app.position))
                    }
                }
            }
        }
    }

    fn fallible_fold_labelled_old(
        &mut self,
        mut labelled_old: vir_low::expression::LabelledOld,
    ) -> Result<vir_low::expression::LabelledOld, Self::Error> {
        std::mem::swap(&mut labelled_old.label, &mut self.label);
        labelled_old.base = self.fallible_fold_expression_boxed(labelled_old.base)?;
        std::mem::swap(&mut labelled_old.label, &mut self.label);
        Ok(labelled_old)
    }

    fn fallible_fold_quantifier_enum(
        &mut self,
        quantifier: vir_low::Quantifier,
    ) -> Result<vir_low::Expression, Self::Error> {
        self.bound_variables.push(&quantifier.variables);
        let quantifier = self.fallible_fold_quantifier(quantifier)?;
        self.bound_variables.pop();
        Ok(vir_low::Expression::Quantifier(quantifier))
    }

    fn fallible_fold_binary_op(
        &mut self,
        mut binary_op: vir_low::expression::BinaryOp,
    ) -> Result<vir_low::expression::BinaryOp, Self::Error> {
        binary_op.left = self.fallible_fold_expression_boxed(binary_op.left)?;
        if binary_op.op_kind == vir_low::BinaryOpKind::Implies {
            self.path_condition.push((*binary_op.left).clone());
        }
        binary_op.right = self.fallible_fold_expression_boxed(binary_op.right)?;
        if binary_op.op_kind == vir_low::BinaryOpKind::Implies {
            self.path_condition.pop();
        }
        Ok(binary_op)
    }

    fn fallible_fold_conditional(
        &mut self,
        mut conditional: vir_low::expression::Conditional,
    ) -> Result<vir_low::expression::Conditional, Self::Error> {
        conditional.guard = self.fallible_fold_expression_boxed(conditional.guard)?;
        self.path_condition.push((*conditional.guard).clone());
        conditional.then_expr = self.fallible_fold_expression_boxed(conditional.then_expr)?;
        self.path_condition.pop();
        self.path_condition
            .push(vir_low::Expression::not((*conditional.guard).clone()));
        conditional.else_expr = self.fallible_fold_expression_boxed(conditional.else_expr)?;
        self.path_condition.pop();
        Ok(conditional)
    }
}

impl<'a, EC: EncoderContext> Purifier<'a, EC> {
    fn resolve_snapshot(
        &mut self,
        function_name: &str,
        arguments: &[vir_low::Expression],
    ) -> SpannedEncodingResult<FindSnapshotResult> {
        if self
            .bound_variables
            .expressions_contains_bound_variables(arguments)
        {
            return Ok(FindSnapshotResult::NotFound);
        }
        let predicate_snapshots = if let Some(label) = &self.label {
            HeapRef::AtLabel(self.predicate_snapshots_at_label.get(label).unwrap())
        } else {
            HeapRef::Current(self.predicate_snapshots)
        };
        let Some(predicate_name) = self.program_context.get_snapshot_predicate(function_name) else {
            // The final snapshot function is already pure and, therefore, is
            // not mapped to a predicate. This is the case for unique_ref final
            // snapshot.
            return Ok(FindSnapshotResult::NotFound);
        };
        predicate_snapshots.find_snapshot(
            predicate_name,
            arguments,
            self.heap_variables,
            self.constraints,
            self.expression_interner,
            self.program_context,
        )
    }
}
