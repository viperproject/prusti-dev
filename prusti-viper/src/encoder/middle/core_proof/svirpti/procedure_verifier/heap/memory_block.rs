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
use log::{debug, error};
use prusti_common::config;
use std::collections::BTreeMap;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, UnaryOperationHelpers},
    low as vir_low,
};

const MEMORY_BLOCK_PERMISSION_MASK_DOMAIN: &str = "MemoryBlockPermissionMask";

#[derive(Default, Clone, Debug)]
pub(in super::super::super::super) struct MemoryBlock {
    permission_mask_version: usize,
}

fn permission_mask_type() -> vir_low::Type {
    vir_low::Type::domain(MEMORY_BLOCK_PERMISSION_MASK_DOMAIN.to_string())
}

fn permission_mask_variable(id: usize) -> SpannedEncodingResult<vir_low::VariableDecl> {
    let name = format!("memory_block_permission_mask${}", id);
    let ty = permission_mask_type();
    let variable = vir_low::VariableDecl::new(name, ty);
    Ok(variable)
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn execute_inhale_memory_block_full(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(predicate.permission.is_full_permission());
        let new_permission_mask_id = self.generate_fresh_id();
        let frame = self.current_frame_mut();
        let memory_block = &mut frame.heap_mut().memory_block;
        let current_permission_mask = permission_mask_variable(memory_block.permission_mask_version)?;
        let new_permission_mask = permission_mask_variable(new_permission_mask_id)?;
        memory_block.permission_mask_version = new_permission_mask_id;
        self.declare_variable(&new_permission_mask)?;
        // // Assume that the old permission is none.
        // let mut current_arguments = vec![current_permission_mask.clone().into()];
        // current_arguments.extend(predicate.arguments.clone());
        // let old_permission = vir_low::Expression::domain_function_call(
        //     MEMORY_BLOCK_PERMISSION_MASK_DOMAIN,
        //     "perm",
        //     current_arguments,
        //     permission_mask_type());
        // let old_permission_is_none = vir_low::Expression::not(
        //     old_permission,
        // );
        // self.assume(&old_permission_is_none)?;
        // Update the permission mask. This also assumes that the old permission is none.
        let mut new_arguments = vec![
            current_permission_mask.clone().into(),
            new_permission_mask.clone().into(),
            ];
        new_arguments.extend(predicate.arguments.clone());
        let update_mask = vir_low::Expression::domain_function_call(
            MEMORY_BLOCK_PERMISSION_MASK_DOMAIN,
            "set_full_permission",
            new_arguments,
            permission_mask_type(),
        );
        self.assume(&update_mask)?;
        // Note: We are keeping the old version of the heap because we are not
        // removing anything.
        Ok(())
    }

    pub(super) fn execute_exhale_memory_block_full(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
        exhale_label: &str,
    ) -> SpannedEncodingResult<()> {
        unimplemented!();
        Ok(())
    }
}
