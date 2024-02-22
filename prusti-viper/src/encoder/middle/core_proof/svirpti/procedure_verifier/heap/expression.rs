use super::super::{
    super::{
        super::transformations::{
            encoder_context::EncoderContext, symbolic_execution_new::ProgramContext,
        },
        smt::{SmtSolver, Sort2SmtWrap},
        VerificationResult, Verifier,
    },
    ProcedureExecutor,
};
use crate::encoder::errors::{SpannedEncodingError, SpannedEncodingResult};
use vir_crate::{
    common::{
        expression::{BinaryOperationHelpers, ExpressionIterator, UnaryOperationHelpers},
        position::Positioned,
    },
    low::{
        self as vir_low, expression::visitors::ExpressionFallibleFolder,
        operations::quantifiers::BoundVariableStack,
    },
};

pub(super) struct ExpressionPurifier<'a, 'b, 'c, EC: EncoderContext> {
    executor: &'a mut ProcedureExecutor<'b, 'c, EC>,
    bound_variables: BoundVariableStack,
    label: Option<String>,
    path_condition: Vec<vir_low::Expression>,
}

impl<'a, 'b, 'c, EC: EncoderContext> ExpressionPurifier<'a, 'b, 'c, EC> {
    pub(super) fn new(executor: &'a mut ProcedureExecutor<'b, 'c, EC>) -> Self {
        Self {
            executor,
            bound_variables: Default::default(),
            label: None,
            path_condition: Vec::new(),
        }
    }
}

impl<'a, 'b, 'c, EC: EncoderContext> ExpressionFallibleFolder
    for ExpressionPurifier<'a, 'b, 'c, EC>
{
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
        unimplemented!();
        // let func_app = self.fallible_fold_func_app(func_app)?;
        // let function = self.program_context.get_function(&func_app.function_name);
        // assert_eq!(function.parameters.len(), func_app.arguments.len());
        // if func_app.context == vir_low::FuncAppContext::QuantifiedPermission {
        //     debug_assert!(matches!(
        //         function.kind,
        //         vir_low::FunctionKind::MemoryBlockBytes | vir_low::FunctionKind::Snap
        //     ));
        //     // This function application is dependent on the quantified resource
        //     // and should not be purified out.
        //     return Ok(vir_low::Expression::FuncApp(func_app));
        // }
        // match function.kind {
        //     vir_low::FunctionKind::CallerFor | vir_low::FunctionKind::SnapRange => {
        //         Ok(vir_low::Expression::FuncApp(func_app))
        //     }
        //     vir_low::FunctionKind::MemoryBlockBytes | vir_low::FunctionKind::Snap => {
        //         match self.resolve_snapshot(&func_app.function_name, &func_app.arguments)? {
        //             FindSnapshotResult::NotFound => Ok(vir_low::Expression::FuncApp(func_app)),
        //             FindSnapshotResult::FoundGuarded {
        //                 snapshot,
        //                 precondition,
        //             } => {
        //                 if let Some(assertion) = precondition {
        //                     let guarded_assertion = vir_low::Expression::implies(
        //                         self.path_condition.clone().into_iter().conjoin(),
        //                         assertion,
        //                     );
        //                     self.guarded_assertions.push(guarded_assertion);
        //                 }
        //                 Ok(vir_low::Expression::local(snapshot, func_app.position))
        //             }
        //             FindSnapshotResult::FoundConditional {
        //                 binding,
        //                 guarded_candidates,
        //             } => {
        //                 assert!(!guarded_candidates.is_empty());
        //                 self.bindings.push(SnapshotBinding {
        //                     guard: self.path_condition.clone().into_iter().conjoin(),
        //                     variable: binding.clone(),
        //                     guarded_candidates,
        //                 });
        //                 Ok(vir_low::Expression::local(binding, func_app.position))
        //             }
        //         }
        //     }
        // }
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
