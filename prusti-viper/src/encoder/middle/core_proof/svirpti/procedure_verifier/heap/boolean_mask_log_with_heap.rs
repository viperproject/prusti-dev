use super::super::{
    super::super::transformations::encoder_context::EncoderContext, ProcedureExecutor,
};
use crate::encoder::errors::SpannedEncodingResult;
use prusti_common::config;
use rustc_hash::FxHashMap;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, ExpressionIterator, UnaryOperationHelpers},
    low::{self as vir_low, operations::ty::Typed},
};

#[derive(Default, Clone, Debug)]
pub(in super::super::super::super) struct BooleanMaskLogWithHeap {
    /// A map from predicate names to the current log entries.
    permission_log_entry: FxHashMap<String, usize>,
    heap_versions: FxHashMap<String, usize>,
}

#[derive(Debug, Clone)]
pub(super) enum LogEntryKind {
    InhaleFull,
    ExhaleFull,
}

#[derive(Debug, Clone)]
pub(super) enum LogEntry {
    InhaleFull(LogEntryFull),
    ExhaleFull(LogEntryFull),
    InhaleQuantified(LogEntryQuantifiedFull),
    ExhaleQuantified(LogEntryQuantifiedFull),
}

#[derive(Debug, Clone)]
pub(super) struct LogEntryFull {
    pub(super) arguments: Vec<vir_low::Expression>,
}

#[derive(Debug, Clone)]
pub(super) struct LogEntryQuantifiedFull {
    pub(super) quantifier_name: Option<String>,
    pub(super) variables: Vec<vir_low::VariableDecl>,
    pub(super) guard: vir_low::Expression,
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
        predicate: vir_low::PredicateAccessPredicate,
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

        // Update Z3 state.
        if !config::svirpti_use_pseudo_boolean_heap() && old_log_entry > 0 {
            let (guard_definitions, check) =
                self.create_permission_check(&predicate.name, &predicate.arguments, old_log_entry)?;
            for definition in guard_definitions {
                self.assume(&definition)?;
            }
            let negated_check = vir_low::Expression::not(check.clone());
            self.assume(&negated_check)?;
        }

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

    pub(super) fn execute_inhale_quantified_boolean_mask_log_with_heap_full(
        &mut self,
        quantifier_name: Option<String>,
        variables: Vec<vir_low::VariableDecl>,
        guard: vir_low::Expression,
        predicate: vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(predicate.permission.is_full_permission());

        // Update local records.
        let frame: &mut crate::encoder::middle::core_proof::svirpti::procedure_verifier::solver_stack::StackFrame = self.current_frame_mut();
        let state = &mut frame.heap_mut().boolean_mask_log_with_heap;
        let log_entry = state.permission_log_entry.get_mut(&predicate.name).unwrap();
        let old_log_entry = *log_entry;
        *log_entry += 1;
        let new_log_entry = *log_entry;

        // The corresponding updating Z3 state step is done in
        // check_quantified_permissions_with_heap_bools because for quantified
        // permissions we need to do it on each instantiation.

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
        let entry = LogEntry::InhaleQuantified(LogEntryQuantifiedFull {
            quantifier_name: quantifier_name.clone(),
            variables: variables.to_vec(),
            guard: guard.clone(),
            arguments: predicate.arguments.clone(),
        });
        entries.push(entry);
        assert_eq!(entries.len(), new_log_entry);

        Ok(())
    }

    fn check_permissions_with_heap_pbge(
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
                LogEntry::InhaleFull(_) | LogEntry::InhaleQuantified(_) => {
                    pbge_arguments.push(plus_one.clone());
                }
                LogEntry::ExhaleFull(_) | LogEntry::ExhaleQuantified(_) => {
                    pbge_arguments.push(minus_one.clone());
                }
            }
        }
        for entry in entries.iter().take(entry_id) {
            match entry {
                LogEntry::InhaleFull(entry) | LogEntry::ExhaleFull(entry) => {
                    let arguments_equal = predicate_arguments
                        .iter()
                        .zip(entry.arguments.iter())
                        .map(|(predicate_argument, entry_argument)| {
                            expr! { [predicate_argument.clone()] == [entry_argument.clone()] }
                        })
                        .conjoin();
                    pbge_arguments.push(arguments_equal);
                }
                LogEntry::InhaleQuantified(entry) | LogEntry::ExhaleQuantified(entry) => {
                    let entry_replacements = if entry.variables.len() == 1
                        && entry.variables[0].name == "element_address"
                    {
                        assert_eq!(&entry.variables[0].ty, predicate_arguments[0].get_type());
                        let mut entry_replacements = FxHashMap::default();
                        entry_replacements.insert(&entry.variables[0], &predicate_arguments[0]);
                        entry_replacements
                    } else {
                        unimplemented!();
                    };
                    let arguments_equal = predicate_arguments
                        .iter()
                        .zip(entry.arguments.iter())
                        .map(|(predicate_argument, entry_argument)| {
                            let entry_argument = entry_argument
                                .clone()
                                .substitute_variables(&entry_replacements);
                            expr! { [predicate_argument.clone()] == [entry_argument] }
                        })
                        .conjoin();
                    let entry_guard = entry
                        .guard
                        .clone()
                        .substitute_variables(&entry_replacements);
                    pbge_arguments.push(expr! { [entry_guard] && [arguments_equal] });
                }
            }
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

    pub(super) fn create_permission_check(
        &mut self,
        predicate_name: &str,
        predicate_arguments: &[vir_low::Expression],
        entry_id: usize,
    ) -> SpannedEncodingResult<(Vec<vir_low::Expression>, vir_low::Expression)> {
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
        fn arguments_equal_quantified(
            predicate_arguments: &[vir_low::Expression],
            entry: &LogEntryQuantifiedFull,
        ) -> vir_low::Expression {
            use vir_low::macros::*;
            let entry_replacements =
                if entry.variables.len() == 1 && entry.variables[0].name == "element_address" {
                    assert_eq!(&entry.variables[0].ty, predicate_arguments[0].get_type());
                    let mut entry_replacements = FxHashMap::default();
                    entry_replacements.insert(&entry.variables[0], &predicate_arguments[0]);
                    entry_replacements
                } else {
                    unimplemented!();
                };
            let arguments_equal = predicate_arguments
                .iter()
                .zip(entry.arguments.iter())
                .map(|(predicate_argument, entry_argument)| {
                    let entry_argument = entry_argument
                        .clone()
                        .substitute_variables(&entry_replacements);
                    expr! { [predicate_argument.clone()] == [entry_argument] }
                })
                .conjoin();
            let entry_guard = entry
                .guard
                .clone()
                .substitute_variables(&entry_replacements);
            expr! { [entry_guard] && [arguments_equal] }
        }
        let entries = self
            .global_heap
            .boolean_mask_log
            .entries
            .get_mut(predicate_name)
            .unwrap();
        let mut entry_iterator = entries.iter().take(entry_id).zip(guards.into_iter());
        // let mut guard_definitions = Vec::with_capacity(entry_id);
        let mut guard_definitions = FxHashMap::default();
        let (first_entry, first_guard) = entry_iterator.next().unwrap();
        let mut check_permissions: vir_low::Expression = match first_entry {
            LogEntry::InhaleFull(entry) => {
                let arguments_equal = arguments_equal(&predicate_arguments, &entry.arguments);
                // guard_definitions.push(expr! { first_guard == [arguments_equal] });
                guard_definitions.insert(arguments_equal, first_guard.clone());
                first_guard.into()
            }
            LogEntry::InhaleQuantified(entry) => {
                let guard_definition = arguments_equal_quantified(&predicate_arguments, entry);
                guard_definitions.insert(guard_definition, first_guard.clone());
                first_guard.into()
            }
            LogEntry::ExhaleFull(_) | LogEntry::ExhaleQuantified(_) => unreachable!(),
        };
        for (entry, guard) in entry_iterator {
            match entry {
                LogEntry::InhaleFull(entry) => {
                    let arguments_equal = arguments_equal(&predicate_arguments, &entry.arguments);
                    let guard_variable = guard_definitions.entry(arguments_equal).or_insert(guard);
                    check_permissions =
                        vir_low::Expression::or(check_permissions, guard_variable.clone().into());
                }
                LogEntry::ExhaleFull(entry) => {
                    let arguments_equal = arguments_equal(&predicate_arguments, &entry.arguments);
                    let guard_variable = guard_definitions.entry(arguments_equal).or_insert(guard);
                    check_permissions = vir_low::Expression::and(
                        check_permissions,
                        vir_low::Expression::not(guard_variable.clone().into()),
                    );
                }
                LogEntry::InhaleQuantified(entry) => {
                    let guard_definition = arguments_equal_quantified(&predicate_arguments, entry);
                    let guard_variable = guard_definitions.entry(guard_definition).or_insert(guard);
                    check_permissions =
                        vir_low::Expression::or(check_permissions, guard_variable.clone().into());
                }
                LogEntry::ExhaleQuantified(entry) => {
                    let guard_definition = arguments_equal_quantified(&predicate_arguments, entry);
                    let guard_variable = guard_definitions.entry(guard_definition).or_insert(guard);
                    check_permissions = vir_low::Expression::and(
                        check_permissions,
                        vir_low::Expression::not(guard_variable.clone().into()),
                    );
                }
            }
        }
        let mut guard_definitions_vec = Vec::new();
        for (definition, guard) in guard_definitions {
            self.declare_variable(&guard)?;
            guard_definitions_vec.push(expr! { guard == [definition] });
        }
        Ok((guard_definitions_vec, check_permissions))
    }

    fn check_permissions_with_heap_bools(
        &mut self,
        predicate_name: &str,
        predicate_arguments: &[vir_low::Expression],
        guard: Option<vir_low::Expression>,
        entry_id: usize,
        full_error_id: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        // Teach Z3 about the non-aliasing assumptions coming from quantified
        // inhales.
        let quantified_inhale_ids = self
            .global_heap
            .boolean_mask_log
            .entries
            .get(predicate_name)
            .unwrap()
            .iter()
            .enumerate()
            .filter_map(|(id, entry)| match entry {
                LogEntry::InhaleQuantified(_) => Some(id),
                _ => None,
            })
            .collect::<Vec<_>>();
        for inhale_entry_id in quantified_inhale_ids {
            if inhale_entry_id == 0 {
                continue;
            }
            let LogEntry::InhaleQuantified(entry) = self.global_heap.boolean_mask_log.entries.get(predicate_name).unwrap()[inhale_entry_id].clone() else {
                unreachable!();
            };
            let replacement_map =
                if entry.variables.len() == 1 && entry.variables[0].name == "element_address" {
                    assert_eq!(&entry.variables[0].ty, predicate_arguments[0].get_type());
                    let mut entry_replacements = FxHashMap::default();
                    entry_replacements.insert(&entry.variables[0], &predicate_arguments[0]);
                    entry_replacements
                } else {
                    unimplemented!();
                };
            let arguments: Vec<_> = entry
                .arguments
                .into_iter()
                .map(|argument| argument.substitute_variables(&replacement_map))
                .collect();
            let (guard_definitions, check) =
                self.create_permission_check(predicate_name, &arguments, inhale_entry_id)?;
            for definition in guard_definitions {
                self.assume(&definition)?;
            }
            let inhale_guard = entry.guard.substitute_variables(&replacement_map);
            let negated_check = vir_low::Expression::not(check.clone());
            let guarded_negated_check = vir_low::Expression::implies(inhale_guard, negated_check);
            self.assume(&guarded_negated_check)?;
        }

        // Construct the check.
        let (guard_definitions, mut check_permissions) =
            self.create_permission_check(predicate_name, predicate_arguments, entry_id)?;
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

    fn check_permissions_with_heap(
        &mut self,
        predicate_name: &str,
        predicate_arguments: &[vir_low::Expression],
        guard: Option<vir_low::Expression>,
        entry_id: usize,
        full_error_id: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        if config::svirpti_use_pseudo_boolean_heap() {
            self.check_permissions_with_heap_pbge(
                predicate_name,
                predicate_arguments,
                guard,
                entry_id,
                full_error_id,
                position,
            )
        } else {
            self.check_permissions_with_heap_bools(
                predicate_name,
                predicate_arguments,
                guard,
                entry_id,
                full_error_id,
                position,
            )
        }
    }

    fn check_quantified_permissions_with_heap_pbge(
        &mut self,
        predicate_name: &str,
        predicate_arguments: &[vir_low::Expression],
        variables: &[vir_low::VariableDecl],
        guard: vir_low::Expression,
        entry_id: usize,
        full_error_id: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        assert!(
            entry_id > 0,
            "TODO: A proper error message that we are exhaling for an empty heap."
        );
        let mut fresh_variables: Vec<vir_low::Expression> = Vec::with_capacity(variables.len());
        for variable in variables {
            let fresh_variable_name = format!("{}${}", variable.name, self.generate_fresh_id());
            let fresh_variable =
                vir_low::VariableDecl::new(fresh_variable_name, variable.ty.clone());
            self.declare_variable(&fresh_variable)?;
            fresh_variables.push(fresh_variable.into());
        }

        let replacements = variables.iter().zip(fresh_variables.iter()).collect();
        let guard = guard.substitute_variables(&replacements);
        let predicate_arguments: Vec<_> = predicate_arguments
            .iter()
            .map(|argument| argument.clone().substitute_variables(&replacements))
            .collect();

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
                LogEntry::InhaleFull(_) | LogEntry::InhaleQuantified(_) => {
                    pbge_arguments.push(plus_one.clone());
                }
                LogEntry::ExhaleFull(_) | LogEntry::ExhaleQuantified(_) => {
                    pbge_arguments.push(minus_one.clone());
                }
            }
        }
        for entry in entries.iter().take(entry_id) {
            match entry {
                LogEntry::InhaleFull(entry) | LogEntry::ExhaleFull(entry) => {
                    let arguments_equal = predicate_arguments
                        .iter()
                        .zip(entry.arguments.iter())
                        .map(|(predicate_argument, entry_argument)| {
                            expr! { [predicate_argument.clone()] == [entry_argument.clone()] }
                        })
                        .conjoin();
                    pbge_arguments.push(arguments_equal);
                }
                LogEntry::InhaleQuantified(entry) | LogEntry::ExhaleQuantified(entry) => {
                    let entry_replacements =
                        entry.variables.iter().zip(fresh_variables.iter()).collect();
                    let arguments_equal = predicate_arguments
                        .iter()
                        .zip(entry.arguments.iter())
                        .map(|(predicate_argument, entry_argument)| {
                            let entry_argument = entry_argument
                                .clone()
                                .substitute_variables(&entry_replacements);
                            expr! { [predicate_argument.clone()] == [entry_argument] }
                        })
                        .conjoin();
                    let entry_guard = entry
                        .guard
                        .clone()
                        .substitute_variables(&entry_replacements);
                    pbge_arguments.push(expr! { [entry_guard] && [arguments_equal] });
                }
            }
        }
        let mut check_permissions = vir_low::Expression::smt_operation_no_pos(
            vir_low::SmtOperationKind::PbQe,
            pbge_arguments,
            vir_low::Type::Bool,
        );
        check_permissions = vir_low::Expression::implies(guard, check_permissions);
        let error = self.create_verification_error_for_expression(
            full_error_id,
            position,
            &check_permissions,
        )?;
        self.assert(check_permissions, error)?;
        Ok(())
    }

    fn check_quantified_permissions_with_heap_bools(
        &mut self,
        predicate_name: &str,
        predicate_arguments: &[vir_low::Expression],
        variables: &[vir_low::VariableDecl],
        guard: vir_low::Expression,
        entry_id: usize,
        full_error_id: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        assert!(
            entry_id > 0,
            "TODO: A proper error message that we are exhaling for an empty heap."
        );
        let mut replacements: Vec<(_, vir_low::Expression)> = Vec::new();
        for variable in variables {
            self.declare_variable(variable)?;
            let fresh_variable_name = format!("{}${}", variable.name, self.generate_fresh_id());
            let fresh_variable =
                vir_low::VariableDecl::new(fresh_variable_name, variable.ty.clone());
            self.declare_variable(&fresh_variable)?;
            replacements.push((variable, fresh_variable.into()));
        }
        let replacement_map: FxHashMap<_, _> = replacements
            .iter()
            .map(|(variable, replacement)| (*variable, replacement))
            .collect();
        let predicate_arguments = predicate_arguments
            .iter()
            .map(|argument| argument.clone().substitute_variables(&replacement_map))
            .collect::<Vec<_>>();

        // Teach Z3 about the non-aliasing assumptions coming from quantified
        // inhales.
        let quantified_inhale_ids = self
            .global_heap
            .boolean_mask_log
            .entries
            .get(predicate_name)
            .unwrap()
            .iter()
            .enumerate()
            .filter_map(|(id, entry)| match entry {
                LogEntry::InhaleQuantified(_) => Some(id),
                _ => None,
            })
            .collect::<Vec<_>>();
        for inhale_entry_id in quantified_inhale_ids {
            if inhale_entry_id == 0 {
                continue;
            }
            let LogEntry::InhaleQuantified(entry) = self.global_heap.boolean_mask_log.entries.get(predicate_name).unwrap()[inhale_entry_id].clone() else {
                unreachable!();
            };
            assert_eq!(&entry.variables, variables, "unimplemented!");
            let arguments: Vec<_> = entry
                .arguments
                .into_iter()
                .map(|argument| argument.substitute_variables(&replacement_map))
                .collect();
            let (guard_definitions, check) =
                self.create_permission_check(predicate_name, &arguments, inhale_entry_id)?;
            for definition in guard_definitions {
                self.assume(&definition)?;
            }
            let inhale_guard = entry.guard.substitute_variables(&replacement_map);
            let negated_check = vir_low::Expression::not(check.clone());
            let guarded_negated_check = vir_low::Expression::implies(inhale_guard, negated_check);
            self.assume(&guarded_negated_check)?;
        }

        // Construct the check.
        let guard = guard.substitute_variables(&replacement_map);
        let (guard_definitions, mut check_permissions) =
            self.create_permission_check(predicate_name, &predicate_arguments, entry_id)?;
        check_permissions = vir_low::Expression::implies(guard, check_permissions);
        let error = self.create_verification_error_for_expression(
            full_error_id,
            position,
            &check_permissions,
        )?;

        self.assert_with_assumptions(&guard_definitions, check_permissions, error)?;
        Ok(())
    }

    fn check_quantified_permissions_with_heap(
        &mut self,
        predicate_name: &str,
        predicate_arguments: &[vir_low::Expression],
        variables: &[vir_low::VariableDecl],
        guard: vir_low::Expression,
        entry_id: usize,
        full_error_id: &str,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        if config::svirpti_use_pseudo_boolean_heap() {
            self.check_quantified_permissions_with_heap_pbge(
                predicate_name,
                predicate_arguments,
                variables,
                guard,
                entry_id,
                full_error_id,
                position,
            )
        } else {
            self.check_quantified_permissions_with_heap_bools(
                predicate_name,
                predicate_arguments,
                variables,
                guard,
                entry_id,
                full_error_id,
                position,
            )
        }
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
        let entry = LogEntry::ExhaleFull(LogEntryFull {
            arguments: predicate.arguments.clone(),
        });
        entries.push(entry);
        assert_eq!(entries.len(), new_log_entry);

        Ok(())
    }

    pub(super) fn execute_exhale_quantified_boolean_mask_log_with_heap_full(
        &mut self,
        quantifier_name: Option<String>,
        variables: Vec<vir_low::VariableDecl>,
        guard: vir_low::Expression,
        predicate: vir_low::PredicateAccessPredicate,
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
        self.check_quantified_permissions_with_heap(
            &predicate.name,
            &predicate.arguments,
            &variables,
            guard.clone(),
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
        let entry = LogEntry::ExhaleQuantified(LogEntryQuantifiedFull {
            quantifier_name: quantifier_name.clone(),
            variables: variables,
            guard: guard.clone(),
            arguments: predicate.arguments.clone(),
        });
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
