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
use vir_crate::low::{self as vir_low};

mod lifetimes;

#[derive(Default, Clone, Debug)]
pub(super) struct Heap {
    lifetime_tokens: lifetimes::LifetimeTokens,
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn execute_inhale_predicate(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let predicate_kind = self.program_context.get_predicate_kind(&predicate.name);
        match predicate_kind {
            vir_low::PredicateKind::MemoryBlock => {
                unimplemented!("inhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::Owned => {
                unimplemented!("inhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::LifetimeToken => {
                self.execute_inhale_lifetime_token(&predicate, position)?;
            }
            vir_low::PredicateKind::DeadLifetimeToken => {
                unimplemented!("inhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::CloseFracRef => {
                unimplemented!("inhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::WithoutSnapshotWhole => {
                unimplemented!("inhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => {
                unimplemented!("inhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::EndBorrowViewShift => {
                unimplemented!("inhale_predicate: {predicate}");
            }
        };
        Ok(())
    }
}
