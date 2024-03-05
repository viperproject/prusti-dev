use super::super::{
    super::super::transformations::encoder_context::EncoderContext, ProcedureExecutor,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::svirpti::procedure_verifier::heap::boolean_mask_log_with_heap::{
        LogEntry, LogEntryFull, LogEntryKind,
    },
};
use prusti_common::config;
use rustc_hash::FxHashMap;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, ExpressionIterator},
    low as vir_low,
};

#[derive(Default, Clone, Debug)]
pub(in super::super::super::super) struct BooleanMaskLogWithoutHeap {
    /// A map from predicate names to the current log entries.
    permission_log_entry: FxHashMap<String, usize>,
}

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn initialise_boolean_mask_log_without_heap(
        &mut self,
        predicate_name: &str,
    ) -> SpannedEncodingResult<()> {
        let heap = self.current_frame_mut().heap_mut();
        assert!(heap
            .boolean_mask_log_without_heap
            .permission_log_entry
            .insert(predicate_name.to_string(), 0usize)
            .is_none());
        assert!(self
            .global_heap
            .boolean_mask_log
            .entries
            .insert(predicate_name.to_string(), vec![])
            .is_none());
        Ok(())
    }

    pub(super) fn execute_inhale_boolean_mask_log_without_heap_full(
        &mut self,
        predicate: vir_low::PredicateAccessPredicate,
        _position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(predicate.permission.is_full_permission());

        // Update local records.
        let frame: &mut crate::encoder::middle::core_proof::svirpti::procedure_verifier::solver_stack::StackFrame = self.current_frame_mut();
        let state = &mut frame.heap_mut().boolean_mask_log_without_heap;
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
        let entry = LogEntry::InhaleFull(LogEntryFull {
            arguments: predicate.arguments.clone(),
        });
        entries.push(entry);
        assert_eq!(entries.len(), new_log_entry);

        Ok(())
    }

    fn check_permissions_without_heap_pbge(
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
            match entry {
                LogEntry::InhaleFull(_) => {
                    pbge_arguments.push(plus_one.clone());
                }
                LogEntry::ExhaleFull(_) => {
                    pbge_arguments.push(minus_one.clone());
                }
                LogEntry::InhaleQuantified(_) => {
                    unimplemented!();
                }
                LogEntry::ExhaleQuantified(_) => {
                    unimplemented!();
                }
            }
        }
        for entry in entries.iter().take(entry_id) {
            unimplemented!();
            // let arguments_equal = predicate_arguments
            //     .iter()
            //     .zip(entry.arguments.iter())
            //     .map(|(predicate_argument, entry_argument)| {
            //         expr! { [predicate_argument.clone()] == [entry_argument.clone()] }
            //     })
            //     .conjoin();
            // pbge_arguments.push(arguments_equal);
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

    fn check_permissions_without_heap_bools(
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
        let mut guards = Vec::with_capacity(entry_id);
        for _ in 0..entry_id {
            let guard_id = self.generate_fresh_id();
            let guard_name = format!("guard${}", guard_id);
            let guard = vir_low::VariableDecl::new(guard_name, vir_low::Type::Bool);
            self.declare_variable(&guard)?;
            guards.push(guard);
        }
        fn arguments_equal(
            predicate_arguments: &[vir_low::Expression],
            entry_arguments: &[vir_low::Expression],
        ) -> vir_low::Expression {
            use vir_low::macros::*;
            predicate_arguments
                .iter()
                .zip(entry_arguments.iter())
                .map(|(predicate_argument, entry_argument)| {
                    expr! { [predicate_argument.clone()] == [entry_argument.clone()] }
                })
                .conjoin()
        }
        let entries = self
            .global_heap
            .boolean_mask_log
            .entries
            .get_mut(predicate_name)
            .unwrap();
        let mut entry_iterator = entries.iter().take(entry_id).zip(guards.into_iter());
        let mut guard_definitions = Vec::with_capacity(entry_id);
        let (first_entry, first_guard) = entry_iterator.next().unwrap();
        let mut check_permissions: vir_low::Expression = match first_entry {
            LogEntry::InhaleFull(entry) => {
                let arguments_equal = arguments_equal(&predicate_arguments, &entry.arguments);
                guard_definitions.push(expr! { first_guard == [arguments_equal] });
                first_guard.into()
            }
            LogEntry::InhaleQuantified(entry) => unimplemented!(),
            LogEntry::ExhaleFull(_) | LogEntry::ExhaleQuantified(_) => unreachable!(),
        };
        for (entry, guard) in entry_iterator {
            match entry {
                LogEntry::InhaleFull(entry) => {
                    let arguments_equal = arguments_equal(&predicate_arguments, &entry.arguments);
                    guard_definitions.push(expr! { guard == [arguments_equal] });
                    check_permissions = vir_low::Expression::or(check_permissions, guard.into());
                }
                LogEntry::ExhaleFull(entry) => {
                    let arguments_equal = arguments_equal(&predicate_arguments, &entry.arguments);
                    guard_definitions.push(expr! { guard == [arguments_equal] });
                    check_permissions = vir_low::Expression::and(check_permissions, guard.into());
                }
                LogEntry::InhaleQuantified(_) => todo!(),
                LogEntry::ExhaleQuantified(_) => todo!(),
            }
        }
        if let Some(guard) = guard {
            check_permissions = vir_low::Expression::implies(guard, check_permissions);
        }
        let error = self.create_verification_error_for_expression(
            full_error_id,
            position,
            &check_permissions,
        )?;
        self.assert_with_assumptions(&guard_definitions, check_permissions, error)?;
        Ok(())
    }

    fn check_permissions_without_heap(
        &mut self,
        predicate_name: &str,
        predicate_arguments: &[vir_low::Expression],
        guard: Option<vir_low::Expression>,
        entry_id: usize,
        full_error_id: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        // FIXME: Avoid code duplication between heap and non-heap versions.
        if config::svirpti_use_pseudo_boolean_heap() {
            self.check_permissions_without_heap_pbge(
                predicate_name,
                predicate_arguments,
                guard,
                entry_id,
                full_error_id,
                position,
            )
        } else {
            self.check_permissions_without_heap_bools(
                predicate_name,
                predicate_arguments,
                guard,
                entry_id,
                full_error_id,
                position,
            )
        }
    }

    pub(super) fn execute_exhale_boolean_mask_log_without_heap_full(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(predicate.permission.is_full_permission());

        // Update local records.
        let frame = self.current_frame_mut();
        let state = &mut frame.heap_mut().boolean_mask_log_without_heap;
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
        self.check_permissions_without_heap(
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
        let entry = LogEntry::ExhaleFull(LogEntryFull {
            arguments: predicate.arguments.clone(),
        });
        entries.push(entry);
        assert_eq!(entries.len(), new_log_entry);

        Ok(())
    }
}
