use super::{BlockHeap, GlobalHeapState, HeapAtLabel, HeapRef};
use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution_new::{
            expression_interner::ExpressionInterner,
            procedure_executor::constraints::BlockConstraints, program_context::ProgramContext,
        },
    },
};
use std::collections::BTreeMap;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, ExpressionIterator},
    low::{self as vir_low, expression::visitors::ExpressionFallibleFolder},
};

pub(in super::super) fn purify_snap_function_calls(
    heap: &BlockHeap,
    global_snapshots: &GlobalHeapState,
    program_context: &ProgramContext<impl EncoderContext>,
    constraints: &mut BlockConstraints,
    expression_interner: &mut ExpressionInterner,
    expression: vir_low::Expression,
) -> SpannedEncodingResult<(vir_low::Expression, Vec<vir_low::Expression>)> {
    let mut purifier = Purifier {
        predicate_snapshots: heap,
        predicate_snapshots_at_label: &global_snapshots.snapshots_at_label,
        constraints,
        expression_interner,
        program_context,
        path_condition: Vec::new(),
        guarded_assertions: Vec::new(),
        label: None,
    };
    let mut expression = purifier.fallible_fold_expression(expression)?;
    if !expression.is_heap_independent() {
        purifier.constraints.saturate_solver()?;
        expression = purifier.fallible_fold_expression(expression)?;
    }
    Ok((expression, purifier.guarded_assertions))
}

struct Purifier<'a, EC: EncoderContext> {
    predicate_snapshots: &'a BlockHeap,
    predicate_snapshots_at_label: &'a BTreeMap<String, HeapAtLabel>,
    constraints: &'a mut BlockConstraints,
    expression_interner: &'a mut ExpressionInterner,
    program_context: &'a ProgramContext<'a, EC>,
    path_condition: Vec<vir_low::Expression>,
    guarded_assertions: Vec<vir_low::Expression>,
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
                if let Some((snapshot_variable, assertion)) =
                    self.resolve_snapshot(&func_app.function_name, &func_app.arguments)?
                {
                    if let Some(assertion) = assertion {
                        let guarded_assertion = vir_low::Expression::implies(
                            self.path_condition.clone().into_iter().conjoin(),
                            assertion,
                        );
                        self.guarded_assertions.push(guarded_assertion);
                    }
                    Ok(vir_low::Expression::local(
                        snapshot_variable,
                        func_app.position,
                    ))
                } else {
                    Ok(vir_low::Expression::FuncApp(func_app))
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
}

impl<'a, EC: EncoderContext> Purifier<'a, EC> {
    fn resolve_snapshot(
        &mut self,
        function_name: &str,
        arguments: &[vir_low::Expression],
    ) -> SpannedEncodingResult<Option<(vir_low::VariableDecl, Option<vir_low::Expression>)>> {
        let predicate_snapshots = if let Some(label) = &self.label {
            HeapRef::AtLabel(self.predicate_snapshots_at_label.get(label).unwrap())
        } else {
            HeapRef::Current(self.predicate_snapshots)
        };
        let Some(predicate_name) = self.program_context.get_snapshot_predicate(function_name) else {
            // The final snapshot function is already pure and,
            // therefore, is not mapped to a predicate.
            return Ok(None);
        };
        predicate_snapshots.find_snapshot(
            predicate_name,
            arguments,
            self.constraints,
            self.expression_interner,
            self.program_context,
        )
    }
}
