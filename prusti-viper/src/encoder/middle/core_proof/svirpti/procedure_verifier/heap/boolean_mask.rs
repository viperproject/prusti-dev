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
use rustc_hash::FxHashMap;
use std::collections::BTreeMap;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, ExpressionIterator, UnaryOperationHelpers},
    low as vir_low,
};

#[derive(Default, Clone, Debug)]
pub(in super::super::super::super) struct MemoryBlock {
    // TODO: Rename to BooleanMaskHeap.
    /// A map from predicate names to their permission mask versions.
    permission_mask_versions: FxHashMap<String, usize>,
    heap_versions: FxHashMap<String, usize>,
}

fn permission_mask_variable_name(predicate_name: &str, id: usize) -> String {
    format!("{}$mask${}", predicate_name, id)
}

fn heap_variable_name(predicate_name: &str, id: usize) -> String {
    format!("{}$heap${}", predicate_name, id)
}

// fn permission_mask_type() -> vir_low::Type {
//     vir_low::Type::domain(MEMORY_BLOCK_PERMISSION_MASK_DOMAIN.to_string())
// }

// fn permission_mask_variable(id: usize) -> SpannedEncodingResult<vir_low::VariableDecl> {
//     let name = format!("memory_block_permission_mask${}", id);
//     let ty = permission_mask_type();
//     let variable = vir_low::VariableDecl::new(name, ty);
//     Ok(variable)
// }

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn initialise_boolean_mask(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<()> {
        let id = self.generate_fresh_id();
        let heap = self.current_frame_mut().heap_mut();
        assert!(heap
            .memory_block
            .permission_mask_versions
            .insert(predicate_name.to_string(), id)
            .is_none());
        assert!(heap
            .memory_block
            .heap_versions
            .insert(predicate_name.to_string(), id)
            .is_none());
        let permission_mask_name = permission_mask_variable_name(predicate_name, id);
        let heap_name = heap_variable_name(predicate_name, id);
        let predicate_info = self.predicate_domains_info.get(predicate_name).unwrap();
        let permission_mask = predicate_info.create_permission_mask_variable(permission_mask_name);
        let heap = predicate_info.create_heap_variable(heap_name);
        self.declare_variable(&permission_mask)?;
        self.declare_variable(&heap)?;
        Ok(())
    }

    pub(super) fn execute_inhale_boolean_mask_full(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(predicate.permission.is_full_permission());

        // Update local records.
        let new_permission_mask_id = self.generate_fresh_id();
        let frame = self.current_frame_mut();
        let memory_block = &mut frame.heap_mut().memory_block;
        let permission_mask_version = memory_block
            .permission_mask_versions
            .get_mut(&predicate.name)
            .unwrap();
        let current_permission_mask_id = *permission_mask_version;
        *permission_mask_version = new_permission_mask_id;

        // Update the SMT solver state.
        let current_permission_mask_name =
            permission_mask_variable_name(&predicate.name, current_permission_mask_id);
        let new_permission_mask_name =
            permission_mask_variable_name(&predicate.name, new_permission_mask_id);

        let predicate_info = self.predicate_domains_info.get(&predicate.name).unwrap();
        let current_permission_mask =
            predicate_info.create_permission_mask_variable(current_permission_mask_name);
        let new_permission_mask =
            predicate_info.create_permission_mask_variable(new_permission_mask_name);

        self.declare_variable(&new_permission_mask)?;

        let update_permissions = predicate_info.set_permissions_to_full(
            &current_permission_mask,
            &new_permission_mask,
            &predicate.arguments,
        );
        // Note: We are keeping the old version of the heap because we are not
        // removing anything.
        self.assume(&update_permissions)?;

        // // // Assume that the old permission is none.
        // // let mut current_arguments = vec![current_permission_mask.clone().into()];
        // // current_arguments.extend(predicate.arguments.clone());
        // // let old_permission = vir_low::Expression::domain_function_call(
        // //     MEMORY_BLOCK_PERMISSION_MASK_DOMAIN,
        // //     "perm",
        // //     current_arguments,
        // //     permission_mask_type());
        // // let old_permission_is_none = vir_low::Expression::not(
        // //     old_permission,
        // // );
        // // self.assume(&old_permission_is_none)?;
        // // Update the permission mask. This also assumes that the old permission is none.
        // let mut new_arguments = vec![
        //     current_permission_mask.clone().into(),
        //     new_permission_mask.clone().into(),
        // ];
        // new_arguments.extend(predicate.arguments.clone());
        // let update_mask = vir_low::Expression::domain_function_call(
        //     MEMORY_BLOCK_PERMISSION_MASK_DOMAIN,
        //     "set_full_permission",
        //     new_arguments,
        //     permission_mask_type(),
        // );
        // self.assume(&update_mask)?;

        Ok(())
    }

    pub(super) fn execute_exhale_boolean_mask_full(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(predicate.permission.is_full_permission());

        // TODO: Avoid code duplication with execute_inhale_boolean_mask_full. BEGIN

        // Update local records.
        let new_permission_mask_id = self.generate_fresh_id();
        let frame = self.current_frame_mut();
        let memory_block = &mut frame.heap_mut().memory_block;
        let permission_mask_version = memory_block
            .permission_mask_versions
            .get_mut(&predicate.name)
            .unwrap();
        let current_permission_mask_id = *permission_mask_version;
        *permission_mask_version = new_permission_mask_id;

        // Update the SMT solver state.
        let current_permission_mask_name =
            permission_mask_variable_name(&predicate.name, current_permission_mask_id);
        let new_permission_mask_name =
            permission_mask_variable_name(&predicate.name, new_permission_mask_id);

        let predicate_info = self.predicate_domains_info.get(&predicate.name).unwrap();
        let current_permission_mask =
            predicate_info.create_permission_mask_variable(current_permission_mask_name);
        let new_permission_mask =
            predicate_info.create_permission_mask_variable(new_permission_mask_name);

        self.declare_variable(&new_permission_mask)?;
        // TODO: END

        let check_permissions =
            predicate_info.check_permissions_full(&current_permission_mask, &predicate.arguments);
        let error = self.create_verification_error_for_expression(
            "exhale.failed:insufficient.permission",
            position,
            &check_permissions,
        )?;
        self.assert(check_permissions, error)?;

        let update_permissions = predicate_info.set_permissions_to_none(
            &current_permission_mask,
            &new_permission_mask,
            &predicate.arguments,
        );
        self.assume(&update_permissions)?;

        // TODO: Havoc heap.

        Ok(())
    }

    pub(super) fn resolve_snapshot_with_check_boolean_mask(
        &mut self,
        path_condition: &[vir_low::Expression],
        label: &Option<String>,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let heap = self.heap_at_label(label);
        let current_permission_mask_id = *heap
            .memory_block
            .permission_mask_versions
            .get(predicate_name)
            .unwrap();
        let current_heap_id = *heap.memory_block.heap_versions.get(predicate_name).unwrap();

        let current_permission_mask_name =
            permission_mask_variable_name(predicate_name, current_permission_mask_id);
        let current_heap_name = heap_variable_name(predicate_name, current_heap_id);
        let predicate_info = self.predicate_domains_info.get(predicate_name).unwrap();
        let current_permission_mask =
            predicate_info.create_permission_mask_variable(current_permission_mask_name);
        let current_heap = predicate_info.create_heap_variable(current_heap_name);

        // Check for sufficient permissions.
        let check_permissions =
            predicate_info.check_permissions_full(&current_permission_mask, arguments);

        // Generate heap snapshot lookup.
        let snapshot = predicate_info.lookup_snapshot(&current_heap, arguments);

        let guard = path_condition.iter().cloned().conjoin();
        let check = vir_low::Expression::implies(guard, check_permissions);
        let error = self.create_verification_error_for_expression(
            "application.precondition:insufficient.permission",
            position,
            &check,
        )?;
        self.assert(check, error)?;

        Ok(snapshot)
    }
}
