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
        if let vir_low::Expression::PredicateAccessPredicate(predicate) = &expression {
            self.execute_exhale_predicate(predicate, position, exhale_label)?;
            return Ok(());
        }
        let expression = expression.clone().wrap_in_old(exhale_label);
        if expression.is_pure() {
            self.assert(expression, position)?;
        } else {
            unimplemented!("exhale: {expression}");
        }
        Ok(())
    }
}
