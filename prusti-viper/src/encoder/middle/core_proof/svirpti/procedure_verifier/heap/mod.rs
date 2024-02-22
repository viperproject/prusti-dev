use self::expression::ExpressionPurifier;
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
use vir_crate::low::{self as vir_low, expression::visitors::ExpressionFallibleFolder};

mod lifetimes;
mod boolean_mask;
mod boolean_mask_without_heap;
mod expression;

#[derive(Default, Clone, Debug)]
pub(super) struct Heap {
    lifetime_tokens: lifetimes::LifetimeTokens,
    boolean_mask_with_heap: boolean_mask::BooleanMaskWithHeap,
    boolean_mask_without_heap: boolean_mask_without_heap::BooleanMaskWithoutHeap,
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn initialise_heap(
        &mut self,
        predicates: &[vir_low::PredicateDecl],
    ) -> SpannedEncodingResult<()> {
        for predicate in predicates {
            match predicate.kind {
                vir_low::PredicateKind::Owned | vir_low::PredicateKind::MemoryBlock => {
                    self.initialise_boolean_mask_with_heap(&predicate.name)?;
                }
                vir_low::PredicateKind::LifetimeToken => {
                    // Nothing to do.
                }
                vir_low::PredicateKind::CloseFracRef => todo!(),
                vir_low::PredicateKind::WithoutSnapshotWhole => todo!(),
                vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => {
                    self.initialise_boolean_mask_without_heap(&predicate.name)?;
                }
                vir_low::PredicateKind::DeadLifetimeToken => {
                    // Nothing to do.
                }
                vir_low::PredicateKind::EndBorrowViewShift => todo!(),
            }
        }
        Ok(())
    }

    pub(super) fn execute_inhale_predicate(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let predicate_kind = self.program_context.get_predicate_kind(&predicate.name);
        match predicate_kind {
            vir_low::PredicateKind::Owned | vir_low::PredicateKind::MemoryBlock => {
                if predicate.permission.is_full_permission() {
                    self.execute_inhale_boolean_mask_with_heap_full(&predicate, position)?;
                } else {
                    // self.execute_inhale_memory_block_fractional(&predicate, position)?;
                    unimplemented!("inhale_predicate: {predicate}");
                }
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

    pub(super) fn execute_exhale_predicate(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let predicate_kind = self.program_context.get_predicate_kind(&predicate.name);
        match predicate_kind {
            vir_low::PredicateKind::Owned | vir_low::PredicateKind::MemoryBlock => {
                if predicate.permission.is_full_permission() {
                    self.execute_exhale_boolean_mask_with_heap_full(&predicate, position)?;
                } else {
                    // self.execute_exhale_memory_block_fractional(&predicate, position)?;
                    unimplemented!("exhale_predicate: {predicate}");
                }
            }
            vir_low::PredicateKind::LifetimeToken => {
                self.execute_exhale_lifetime_token(&predicate, position)?;
            }
            vir_low::PredicateKind::DeadLifetimeToken => {
                unimplemented!("exhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::CloseFracRef => {
                unimplemented!("exhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::WithoutSnapshotWhole => {
                unimplemented!("exhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => {
                unimplemented!("exhale_predicate: {predicate}");
            }
            vir_low::PredicateKind::EndBorrowViewShift => {
                unimplemented!("exhale_predicate: {predicate}");
            }
        };
        Ok(())
    }

    pub(super) fn desugar_heap_expression(
        &mut self,
        expression: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut purifier = ExpressionPurifier::new(self);
        purifier.fallible_fold_expression(expression)
    }

    fn resolve_snapshot_with_check_predicate(
        &mut self,
        path_condition: &[vir_low::Expression],
        label: &Option<String>,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let predicate_kind = self.program_context.get_predicate_kind(predicate_name);
        let snapshot = match predicate_kind {
            vir_low::PredicateKind::MemoryBlock | vir_low::PredicateKind::Owned => self
                .resolve_snapshot_with_check_boolean_mask_with_heap(
                    path_condition,
                    label,
                    predicate_name,
                    arguments,
                    position,
                )?,
            vir_low::PredicateKind::LifetimeToken => todo!(),
            vir_low::PredicateKind::CloseFracRef => todo!(),
            vir_low::PredicateKind::WithoutSnapshotWhole => todo!(),
            vir_low::PredicateKind::WithoutSnapshotWholeNonAliased => todo!(),
            vir_low::PredicateKind::DeadLifetimeToken => todo!(),
            vir_low::PredicateKind::EndBorrowViewShift => todo!(),
        };
        Ok(snapshot)
    }

    pub(super) fn save_state(&mut self, label: String) -> SpannedEncodingResult<()> {
        let frame = self.current_frame_mut();
        let heap = frame.heap().clone();
        frame.log_saved_state_label(label.clone())?;
        assert!(self.saved_heaps.insert(label, heap).is_none());
        Ok(())
    }

    pub(super) fn heap_at_label(&self, label: &Option<String>) -> &Heap {
        match label {
            Some(label) => self.saved_heaps.get(label).unwrap(),
            None => self.current_frame().heap(),
        }
    }
}
