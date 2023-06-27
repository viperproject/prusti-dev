use super::{super::super::super::encoder_context::EncoderContext, ProcedureExecutor};
use crate::encoder::errors::SpannedEncodingResult;

use vir_crate::low::{self as vir_low};

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn execute_exhale(
        &mut self,
        expression: &vir_low::Expression,
        position: vir_low::Position,
        exhale_label: &str,
    ) -> SpannedEncodingResult<()> {
        if let vir_low::Expression::BinaryOp(expression) = expression {
            if expression.op_kind == vir_low::BinaryOpKind::And {
                self.execute_exhale(&expression.left, position, exhale_label)?;
                self.execute_exhale(&expression.right, position, exhale_label)?;
                return Ok(());
            }
        }
        let expression = self.simplify_expression(expression, position)?;
        if let vir_low::Expression::PredicateAccessPredicate(predicate) = &expression {
            self.exhale_predicate(predicate.clone(), position)?;
            return Ok(());
        }
        let expression = expression.wrap_in_old(exhale_label);
        for predicate_name in expression.collect_access_predicate_names() {
            self.prepare_for_unhandled_exhale(&predicate_name, position)?;
        }
        self.try_assume_heap_independent_conjuncts(&expression)?;
        self.add_statement(vir_low::Statement::exhale(expression, position))?;
        Ok(())
    }
}
