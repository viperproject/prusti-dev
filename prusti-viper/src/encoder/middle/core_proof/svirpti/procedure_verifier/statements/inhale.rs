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
        if expression.is_pure() {
            self.assume(expression)?;
        } else if let vir_low::Expression::PredicateAccessPredicate(predicate) = &expression {
            self.execute_inhale_predicate(predicate, position)?;
        } else {
            unimplemented!("inhale: {expression}");
        }
        Ok(())
    }
}
