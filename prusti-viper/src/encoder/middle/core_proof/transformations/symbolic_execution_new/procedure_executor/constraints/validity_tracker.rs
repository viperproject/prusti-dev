use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution_new::expression_interner::{
        ExpressionId, ExpressionInterner,
    },
};
use rustc_hash::FxHashSet;
use vir_crate::{
    common::expression::SyntacticEvaluation,
    low::{self as vir_low, operations::ty::Typed},
};

#[derive(Clone, Default, Debug)]
pub(super) struct ValidityTracker {
    /// The set of values that are known to be valid at this point.
    valid_expressions: FxHashSet<ExpressionId>,
}

impl std::fmt::Display for ValidityTracker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "valid expressions")?;
        for id in &self.valid_expressions {
            writeln!(f, "  {id:?}",)?;
        }
        Ok(())
    }
}

impl ValidityTracker {
    pub(super) fn merge(&mut self, other: &Self) -> SpannedEncodingResult<()> {
        // Something is valid only if it is valid in both states. Therefore, we
        // intersect.
        self.valid_expressions
            .retain(|id| other.valid_expressions.contains(id));
        Ok(())
    }

    // pub(super) fn assume(
    //     &mut self,
    //     expression_interner: &mut ExpressionInterner,
    //     expression: &vir_low::Expression,
    //     value: bool,
    // ) -> SpannedEncodingResult<()> {
    //     if !expression.is_heap_independent() {
    //         return Ok(());
    //     }
    //     match expression {
    //         // FIXME: Do not rely on string comparisons. Use program_context
    //         // instead.
    //         vir_low::Expression::DomainFuncApp(domain_func_app)
    //             if domain_func_app.function_name.starts_with("valid$") =>
    //         {
    //             assert_eq!(domain_func_app.arguments.len(), 1);
    //             assert!(value, "Not valid?: {expression}");
    //             let expression_id = expression_interner
    //                 .intern_snapshot_expression(&domain_func_app.arguments[0])?;
    //             eprintln!("Assuming {expression_id:?} is valid: {expression}");
    //             self.valid_expressions.insert(expression_id);
    //         }
    //         _ => {}
    //     }
    //     Ok(())
    // }

    pub(super) fn assume_expression_valid(
        &mut self,
        expression_interner: &mut ExpressionInterner,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        debug_assert!(expression.is_heap_independent());
        let expression_id = expression_interner.intern_snapshot_expression(expression)?;
        self.valid_expressions.insert(expression_id);
        Ok(())
    }

    pub(super) fn is_valid(&self, expression_id: ExpressionId) -> SpannedEncodingResult<bool> {
        Ok(self.valid_expressions.contains(&expression_id))
    }

    pub(super) fn is_valid_expression(
        &self,
        expression_interner: &mut ExpressionInterner,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<bool> {
        debug_assert!(expression.is_heap_independent());
        let expression_id = expression_interner.intern_snapshot_expression(expression)?;
        self.is_valid(expression_id)
    }
}
