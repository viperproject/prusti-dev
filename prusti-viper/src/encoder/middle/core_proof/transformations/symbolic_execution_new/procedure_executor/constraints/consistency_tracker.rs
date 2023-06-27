use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::symbolic_execution_new::expression_interner::ExpressionId,
};
use rustc_hash::FxHashSet;
use vir_crate::{
    common::expression::SyntacticEvaluation,
    low::{self as vir_low, operations::ty::Typed},
};

#[derive(Clone, Default, Debug)]
pub(super) struct ConsistencyTracker {
    is_inconsistent: bool,
    /// The set of expressions that are known to be definitely true at this
    /// point.
    definitely_true: FxHashSet<ExpressionId>,
    /// The set of expressions that are known to be definitely false at this
    /// point.
    definitely_false: FxHashSet<ExpressionId>,
}

impl std::fmt::Display for ConsistencyTracker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "is_inconsistent: {}", self.is_inconsistent)?;
        writeln!(f, "definitely true",)?;
        for id in &self.definitely_true {
            writeln!(f, "  {id:?}",)?;
        }
        writeln!(f, "definitely false",)?;
        for id in &self.definitely_false {
            writeln!(f, "  {id:?}",)?;
        }
        Ok(())
    }
}

impl ConsistencyTracker {
    pub(super) fn is_inconsistent(&self) -> SpannedEncodingResult<bool> {
        Ok(self.is_inconsistent)
    }

    pub(super) fn is_definitely_true(
        &self,
        expression: &vir_low::Expression,
        expression_id: ExpressionId,
    ) -> SpannedEncodingResult<bool> {
        Ok(self.definitely_true.contains(&expression_id) || expression.is_true())
    }

    pub(super) fn is_definitely_false(
        &self,
        expression: &vir_low::Expression,
        expression_id: ExpressionId,
    ) -> SpannedEncodingResult<bool> {
        Ok(self.definitely_false.contains(&expression_id) || expression.is_false())
    }

    pub(super) fn merge(&mut self, other: &Self) -> SpannedEncodingResult<()> {
        // Something is definitely true or false only if it is true or false on
        // both states. Therefore, we intersect.
        self.definitely_true
            .retain(|id| other.definitely_true.contains(id));
        self.definitely_false
            .retain(|id| other.definitely_false.contains(id));
        Ok(())
    }

    pub(super) fn assume_false(&mut self) -> SpannedEncodingResult<()> {
        self.is_inconsistent = true;
        Ok(())
    }

    pub(super) fn assume(
        &mut self,
        expression: &vir_low::Expression,
        expression_id: ExpressionId,
        value: bool,
    ) -> SpannedEncodingResult<()> {
        debug_assert!(expression.is_heap_independent());
        if value {
            if self.is_definitely_false(expression, expression_id)? {
                self.is_inconsistent = true;
            } else {
                self.definitely_true.insert(expression_id);
            }
        } else if self.is_definitely_true(expression, expression_id)? {
            self.is_inconsistent = true;
        } else {
            self.definitely_false.insert(expression_id);
        }
        Ok(())
    }

    pub(super) fn assuming_makes_inconsistent(
        &self,
        expression_id: ExpressionId,
        value: bool,
    ) -> SpannedEncodingResult<bool> {
        let is_inconsistent = if value {
            self.definitely_false.contains(&expression_id)
        } else {
            self.definitely_true.contains(&expression_id)
        };
        Ok(is_inconsistent)
    }
}
