use super::{
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
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
};

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn assume(&mut self, expression: &vir_low::Expression) -> SpannedEncodingResult<()> {
        self.smt_solver.assert(expression).unwrap(); // TODO: handle error
        Ok(())
    }
}
