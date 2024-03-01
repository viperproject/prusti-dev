use super::super::{
    super::super::transformations::encoder_context::EncoderContext, ProcedureExecutor,
};
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::low::{self as vir_low};

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn execute_exhale(
        &mut self,
        expression: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        match expression {
            vir_low::Expression::BinaryOp(expression)
                if expression.op_kind == vir_low::BinaryOpKind::And =>
            {
                self.execute_exhale(*expression.left, position)?;
                self.execute_exhale(*expression.right, position)?;
                return Ok(());
            }
            _ => (),
        }
        if let vir_low::Expression::PredicateAccessPredicate(predicate) = &expression {
            self.execute_exhale_predicate(predicate, position)?;
            return Ok(());
        }
        if expression.is_pure() {
            let expression = self.desugar_heap_expression(expression)?;
            let error = self.create_verification_error_for_expression(
                "exhale.failed:assertion.false",
                position,
                &expression,
            )?;
            self.assert(expression, error)?;
        } else {
            match expression {
                vir_low::Expression::Quantifier(vir_low::Quantifier {
                    name,
                    kind: vir_low::QuantifierKind::ForAll,
                    variables,
                    triggers: _,
                    body:
                        box vir_low::Expression::BinaryOp(vir_low::BinaryOp {
                            op_kind: vir_low::BinaryOpKind::Implies,
                            left: box guard,
                            right: box vir_low::Expression::PredicateAccessPredicate(mut predicate),
                            position: _,
                        }),
                    position,
                }) => {
                    predicate.arguments = self.desugar_heap_expressions(predicate.arguments)?;
                    let guard = self.desugar_heap_expression(guard)?;
                    self.execute_exhale_quantified_predicate(
                        name, variables, guard, predicate, position,
                    )?;
                }
                _ => {
                    unimplemented!("exhale: {expression}");
                }
            }
        }
        Ok(())
    }
}
