use super::super::{
    super::super::transformations::encoder_context::EncoderContext, ProcedureExecutor,
};
use crate::encoder::errors::SpannedEncodingResult;
use rustc_hash::FxHashMap;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, ExpressionIterator},
    low as vir_low,
};

#[derive(Default, Clone, Debug)]
pub(in super::super::super::super) struct BooleanMaskLogWithHeap {
    /// A map from predicate names to the current log entries.
    permission_log_entry: FxHashMap<String, usize>,
    heap_versions: FxHashMap<String, usize>,
}

#[derive(Debug)]
pub(super) enum LogEntryKind {
    InhaleFull,
    ExhaleFull,
}

#[derive(Debug)]
pub(super) struct LogEntry {
    pub(super) kind: LogEntryKind,
    pub(super) arguments: Vec<vir_low::Expression>,
}

#[derive(Default, Debug)]
pub(in super::super::super::super) struct BooleanMaskLog {
    pub(super) entries: FxHashMap<String, Vec<LogEntry>>,
}

fn heap_variable_name(predicate_name: &str, id: usize) -> String {
    format!("{}$heap${}", predicate_name, id)
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn initialise_boolean_mask_log_with_heap(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<()> {
        let id = self.generate_fresh_id();
        let heap = self.current_frame_mut().heap_mut();
        assert!(heap
            .boolean_mask_log_with_heap
            .permission_log_entry
            .insert(predicate_name.to_string(), 0usize)
            .is_none());
        assert!(heap
            .boolean_mask_log_with_heap
            .heap_versions
            .insert(predicate_name.to_string(), id)
            .is_none());
        assert!(self
            .global_heap
            .boolean_mask_log
            .entries
            .insert(predicate_name.to_string(), vec![])
            .is_none());
        let heap_name = heap_variable_name(predicate_name, id);
        let predicate_info = self
            .predicate_domains_info
            .get_with_heap(predicate_name)
            .unwrap();
        let heap = predicate_info.create_heap_variable(heap_name);
        self.declare_variable(&heap)?;
        Ok(())
    }

    pub(super) fn execute_inhale_boolean_mask_log_with_heap_full(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        _position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(predicate.permission.is_full_permission());

        // Update local records.
        let frame: &mut crate::encoder::middle::core_proof::svirpti::procedure_verifier::solver_stack::StackFrame = self.current_frame_mut();
        let state = &mut frame.heap_mut().boolean_mask_log_with_heap;
        let log_entry = state.permission_log_entry.get_mut(&predicate.name).unwrap();
        let old_log_entry = *log_entry;
        *log_entry += 1;
        let new_log_entry = *log_entry;

        // Update the global heap.
        let entries = self
            .global_heap
            .boolean_mask_log
            .entries
            .get_mut(&predicate.name)
            .unwrap();
        if entries.len() > old_log_entry {
            entries.truncate(old_log_entry);
        }
        assert_eq!(entries.len(), old_log_entry);
        let entry = LogEntry {
            kind: LogEntryKind::InhaleFull,
            arguments: predicate.arguments.clone(),
        };
        entries.push(entry);
        assert_eq!(entries.len(), new_log_entry);

        Ok(())
    }

    fn check_permissions_with_heap(
        &mut self,
        predicate_name: &str,
        predicate_arguments: &[vir_low::Expression],
        guard: Option<vir_low::Expression>,
        entry_id: usize,
        full_error_id: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        assert!(
            entry_id > 0,
            "TODO: A proper error message that we are exhaling for an empty heap."
        );
        let entries = self
            .global_heap
            .boolean_mask_log
            .entries
            .get_mut(predicate_name)
            .unwrap();
        let mut pbge_arguments = Vec::with_capacity(entry_id);
        let plus_one: vir_low::Expression = 1.into();
        let minus_one: vir_low::Expression = (-1).into();
        for entry in entries.iter().take(entry_id) {
            match entry.kind {
                LogEntryKind::InhaleFull => {
                    pbge_arguments.push(plus_one.clone());
                }
                LogEntryKind::ExhaleFull => {
                    pbge_arguments.push(minus_one.clone());
                }
            }
        }
        for entry in entries.iter().take(entry_id) {
            let arguments_equal = predicate_arguments
                .iter()
                .zip(entry.arguments.iter())
                .map(|(predicate_argument, entry_argument)| {
                    expr! { [predicate_argument.clone()] == [entry_argument.clone()] }
                })
                .conjoin();
            pbge_arguments.push(arguments_equal);
        }
        let mut check_permissions = vir_low::Expression::smt_operation_no_pos(
            vir_low::SmtOperationKind::PbQe,
            pbge_arguments,
            vir_low::Type::Bool,
        );
        if let Some(guard) = guard {
            check_permissions = vir_low::Expression::implies(guard, check_permissions);
        }
        let error = self.create_verification_error_for_expression(
            full_error_id,
            position,
            &check_permissions,
        )?;
        self.assert(check_permissions, error)?;
        Ok(())
    }

    pub(super) fn execute_exhale_boolean_mask_log_with_heap_full(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(predicate.permission.is_full_permission());

        // Update local records.
        let frame = self.current_frame_mut();
        let state = &mut frame.heap_mut().boolean_mask_log_with_heap;
        let log_entry = state.permission_log_entry.get_mut(&predicate.name).unwrap();
        let old_log_entry = *log_entry;
        *log_entry += 1;
        let new_log_entry = *log_entry;

        // Update the global heap.
        let entries = self
            .global_heap
            .boolean_mask_log
            .entries
            .get_mut(&predicate.name)
            .unwrap();
        if entries.len() > old_log_entry {
            entries.truncate(old_log_entry);
        }
        assert_eq!(entries.len(), old_log_entry);
        self.check_permissions_with_heap(
            &predicate.name,
            &predicate.arguments,
            None,
            old_log_entry,
            "exhale.failed:insufficient.permission",
            position,
        )?;
        let entries = self
            .global_heap
            .boolean_mask_log
            .entries
            .get_mut(&predicate.name)
            .unwrap();
        let entry = LogEntry {
            kind: LogEntryKind::ExhaleFull,
            arguments: predicate.arguments.clone(),
        };
        entries.push(entry);
        assert_eq!(entries.len(), new_log_entry);

        Ok(())
    }

    pub(super) fn resolve_snapshot_with_check_boolean_mask_log_with_heap(
        &mut self,
        path_condition: &[vir_low::Expression],
        label: &Option<String>,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let heap = self.heap_at_label(label);
        let current_log_entry = *heap
            .boolean_mask_log_with_heap
            .permission_log_entry
            .get(predicate_name)
            .unwrap();
        let current_heap_id = *heap
            .boolean_mask_log_with_heap
            .heap_versions
            .get(predicate_name)
            .unwrap();

        let current_heap_name = heap_variable_name(predicate_name, current_heap_id);
        let predicate_info = self
            .predicate_domains_info
            .get_with_heap(predicate_name)
            .unwrap();
        let current_heap = predicate_info.create_heap_variable(current_heap_name);

        // Check for sufficient permissions.
        let guard = path_condition.iter().cloned().conjoin();
        self.check_permissions_with_heap(
            predicate_name,
            arguments,
            Some(guard),
            current_log_entry,
            "application.precondition:insufficient.permission",
            position,
        )?;

        // Generate heap snapshot lookup.
        let snapshot = predicate_info.lookup_snapshot(&current_heap, arguments);

        Ok(snapshot)
    }
}
