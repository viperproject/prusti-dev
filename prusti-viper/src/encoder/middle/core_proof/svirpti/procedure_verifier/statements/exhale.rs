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
            self.assert(expression, position)?;
        } else {
            unimplemented!("exhale: {expression}");
        }
        Ok(())
    }
}
