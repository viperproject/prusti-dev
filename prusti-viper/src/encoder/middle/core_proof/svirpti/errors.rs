use super::{super::transformations::encoder_context::EncoderContext, ProcedureExecutor};
use crate::encoder::errors::SpannedEncodingResult;
use vir_crate::low as vir_low;

#[derive(Debug)]
pub(crate) struct VerificationError {
    full_id: String,
    position: vir_low::Position,
    message: String,
}

impl VerificationError {
    pub(crate) fn as_viper_verification_error(&self) -> viper::VerificationError {
        viper::VerificationError {
            full_id: self.full_id.clone(),
            pos_id: None,
            offending_pos_id: Some(self.position.id.to_string()),
            reason_pos_id: None,
            message: self.message.clone(),
            counterexample: None,
        }
    }
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn create_verification_error_for_expression(
        &self,
        full_id: &str,
        position: vir_low::Position,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<VerificationError> {
        let frame = self.current_frame();
        let trace = self.current_execution_trace()?;
        let message = format!(
            "Expression `{}` in program {} procedure {} basic block {} \
             statement {} failed to verify. Trace: {:?}.",
            expression,
            self.source_filename(),
            self.procedure_name(),
            frame.label().name,
            frame.statement_index(),
            trace,
        );
        Ok(VerificationError {
            full_id: full_id.to_string(),
            position,
            message,
        })
    }
}
