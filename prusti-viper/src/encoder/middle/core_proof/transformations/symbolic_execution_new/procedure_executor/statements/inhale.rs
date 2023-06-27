use super::{super::super::super::encoder_context::EncoderContext, ProcedureExecutor};
use crate::encoder::errors::SpannedEncodingResult;

use vir_crate::low::{self as vir_low};

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn execute_inhale(
        &mut self,
        expression: &vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        if let vir_low::Expression::BinaryOp(expression) = expression {
            if expression.op_kind == vir_low::BinaryOpKind::And {
                self.execute_inhale(&expression.left, position)?;
                self.execute_inhale(&expression.right, position)?;
                return Ok(());
            }
        }
        let expression = self.simplify_expression(expression, position)?;
        if let vir_low::Expression::PredicateAccessPredicate(predicate) = &expression {
            self.inhale_predicate(predicate.clone(), position)?;
            return Ok(());
        }
        // for predicate_name in expression.collect_access_predicate_names() {
        //     self.mark_predicate_instances_seen_qp_inhale(&predicate_name)?;
        // }
        self.try_assume_heap_independent_conjuncts(&expression)?;
        self.add_statement(vir_low::Statement::inhale(expression, position))?;
        Ok(())
    }
}
