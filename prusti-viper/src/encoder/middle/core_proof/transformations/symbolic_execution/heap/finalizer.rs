use super::{
    lifetime_tokens::LifetimeTokens,
    predicate_snapshots::{
        check_non_aliased_snap_calls_purified, purify_snap_calls, purify_snap_calls_vec_with_retry,
        PredicateSnapshots,
    },
    state::{PredicateInstance, PredicateInstanceState},
    HeapEntry, HeapState, Location,
};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution::{egg::EGraphState, program_context::ProgramContext, trace::Trace},
    },
};
use prusti_common::config;
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

pub(super) struct TraceFinalizer<'a, EC: EncoderContext> {
    source_filename: &'a str,
    procedure_name: &'a str,
    purification_failure_count: usize,
    final_state: &'a HeapState,
    trace: Vec<vir_low::Statement>,
    new_variables: Vec<vir_low::VariableDecl>,
    new_labels: Vec<vir_low::Label>,
    predicate_snapshots: PredicateSnapshots,
    predicate_snapshots_at_label: BTreeMap<String, PredicateSnapshots>,
    lifetime_tokens: LifetimeTokens,
    solver: &'a mut EGraphState,
    program: &'a ProgramContext<'a, EC>,
}

impl<'a, EC: EncoderContext> TraceFinalizer<'a, EC> {
    pub(super) fn new(
        source_filename: &'a str,
        procedure_name: &'a str,
        final_state: &'a HeapState,
        solver: &'a mut EGraphState,
        program: &'a ProgramContext<'a, EC>,
    ) -> Self {
        Self {
            source_filename,
            procedure_name,
            purification_failure_count: 0,
            final_state,
            trace: Vec::new(),
            new_variables: Vec::new(),
            new_labels: Vec::new(),
            predicate_snapshots: Default::default(),
            predicate_snapshots_at_label: Default::default(),
            lifetime_tokens: Default::default(),
            solver,
            program,
        }
    }

    pub(super) fn into_trace(self) -> Trace {
        let mut variables = self.new_variables;
        variables.extend(self.predicate_snapshots.into_variables());
        variables.extend(self.lifetime_tokens.into_variables());
        Trace {
            statements: self.trace,
            variables,
            labels: self.new_labels,
        }
    }

    pub(super) fn trace_len(&self) -> usize {
        self.trace.len()
    }

    pub(super) fn trace_suffix(&self, checkpoint: usize) -> &[vir_low::Statement] {
        self.trace[checkpoint..].as_ref()
    }

    pub(super) fn add_variables(
        &mut self,
        new_variables: &[vir_low::VariableDecl],
    ) -> SpannedEncodingResult<()> {
        self.new_variables.extend_from_slice(new_variables);
        Ok(())
    }

    pub(super) fn add_labels(
        &mut self,
        new_labels: &[vir_low::Label],
    ) -> SpannedEncodingResult<()> {
        self.new_labels.extend_from_slice(new_labels);
        Ok(())
    }

    pub(super) fn add_entry(
        &mut self,
        location: Location,
        entry: &HeapEntry,
    ) -> SpannedEncodingResult<()> {
        match entry {
            HeapEntry::Comment(statement) => {
                self.trace
                    .push(vir_low::Statement::Comment(statement.clone()));
            }
            HeapEntry::Label(statement) => {
                self.save_state(statement.label.clone());
                self.trace
                    .push(vir_low::Statement::Label(statement.clone()));
            }
            HeapEntry::InhalePredicate(predicate, position) => {
                let predicate_kind = self.program.get_predicate_kind(&predicate.name);
                let arguments = purify_snap_calls_vec_with_retry(
                    &self.predicate_snapshots,
                    &self.predicate_snapshots_at_label,
                    self.solver,
                    self.program,
                    predicate.arguments.clone(),
                )?;
                if predicate_kind == vir_low::PredicateKind::LifetimeToken {
                    self.purify_lifetime_token_inhale(predicate, *position)?;
                } else if let Some(predicate_instance) =
                    self.is_purified_inhale(location, predicate)
                {
                    let snapshot = predicate_instance.snapshot.clone();
                    if config::report_symbolic_execution_purification() {
                        self.trace.push(vir_low::Statement::comment(format!(
                            "purified out: {entry}"
                        )));
                    }
                    if let Some(snapshot_variable_name) = snapshot {
                        self.predicate_snapshots.register_predicate_snapshot(
                            self.program,
                            &predicate.name,
                            arguments,
                            snapshot_variable_name,
                        );
                    } else {
                        self.predicate_snapshots.create_predicate_snapshot(
                            self.program,
                            &predicate.name,
                            arguments,
                        );
                    }
                } else {
                    self.report_purification_failure(*position)?;
                    self.trace.push(vir_low::Statement::inhale(
                        vir_low::Expression::predicate_access_predicate(
                            predicate.name.clone(),
                            arguments,
                            *(predicate.permission).clone(),
                            predicate.position,
                        ),
                        *position,
                    ));
                }
            }
            HeapEntry::ExhalePredicate(predicate, position) => {
                let predicate_kind = self.program.get_predicate_kind(&predicate.name);
                let arguments = purify_snap_calls_vec_with_retry(
                    &self.predicate_snapshots,
                    &self.predicate_snapshots_at_label,
                    self.solver,
                    self.program,
                    predicate.arguments.clone(),
                )?;
                if predicate_kind == vir_low::PredicateKind::LifetimeToken {
                    self.purify_lifetime_token_exhale(predicate, *position)?;
                } else if self.is_purified_exhale(location, predicate) {
                    if config::report_symbolic_execution_purification() {
                        self.trace.push(vir_low::Statement::comment(format!(
                            "purified out: {entry}"
                        )));
                    }
                    self.predicate_snapshots.destroy_predicate_snapshot(
                        &predicate.name,
                        &arguments,
                        self.solver,
                    )?;
                } else {
                    if predicate_kind == vir_low::PredicateKind::CloseFracRef {
                        self.try_assert_frac_ref_snapshot_equality(predicate, *position)?;
                    }
                    self.report_purification_failure(*position)?;
                    self.trace.push(vir_low::Statement::exhale(
                        vir_low::Expression::predicate_access_predicate(
                            predicate.name.clone(),
                            arguments,
                            *(predicate.permission).clone(),
                            predicate.position,
                        ),
                        *position,
                    ));
                }
            }
            HeapEntry::InhaleGeneric(statement) => {
                // eprintln!("InhaleGeneric: {}", statement.expression);
                self.add_expression_entry(
                    &statement.expression,
                    statement.position,
                    vir_low::Statement::inhale,
                )?;
            }
            HeapEntry::ExhaleGeneric(statement) => {
                self.add_expression_entry(
                    &statement.expression,
                    statement.position,
                    vir_low::Statement::exhale,
                )?;
            }
            HeapEntry::Assume(statement) => {
                self.add_expression_entry(
                    &statement.expression,
                    statement.position,
                    vir_low::Statement::assume,
                )?;
            }
            HeapEntry::Assert(statement) => {
                self.add_expression_entry(
                    &statement.expression,
                    statement.position,
                    vir_low::Statement::assert,
                )?;
            }
        }
        Ok(())
    }

    fn add_expression_entry(
        &mut self,
        expression: &vir_low::Expression,
        position: vir_low::Position,
        constructor: fn(vir_low::Expression, vir_low::Position) -> vir_low::Statement,
    ) -> SpannedEncodingResult<()> {
        // let simplified_expression = simplify_expression(expression.clone(), self.program, self.solver)?;
        // if &simplified_expression != expression {
        //     self.solver.intern_heap_independent_subexpressions(&simplified_expression)?;
        // }
        let simplified_expression = expression.clone();
        let expression = self.purify_snap_calls(simplified_expression)?;
        if !check_non_aliased_snap_calls_purified(&expression, self.program) {
            // Purification failed, this should be unreachable.
            self.trace.push(vir_low::Statement::comment(format!(
                "Failed to purify: {}",
                expression
            )));
            self.trace
                .push(vir_low::Statement::assert(false.into(), position));
        }
        // assert!(check_non_aliased_snap_calls_purified(
        //     &expression,
        //     self.program
        // ));
        self.trace.push(constructor(expression, position));
        Ok(())
    }

    fn report_purification_failure(
        &mut self,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        if config::report_symbolic_execution_failures() {
            prusti_common::report::log::report_with_writer(
                "symbex_purification_failures",
                format!(
                    "{}.{}.{}.dot",
                    self.source_filename, self.procedure_name, self.purification_failure_count
                ),
                |writer| self.solver.to_graphviz(writer).unwrap(),
            );
            self.trace.push(vir_low::Statement::comment(format!(
                "Failed to purify. Failure id: {}",
                self.purification_failure_count
            )));
            self.trace
                .push(vir_low::Statement::assert(false.into(), position));
            self.purification_failure_count += 1;
        }
        Ok(())
    }

    fn is_purified_inhale(
        &self,
        location: Location,
        predicate: &vir_low::expression::PredicateAccessPredicate,
    ) -> Option<&PredicateInstance> {
        if let Some(predicate_state) = self.final_state.get_predicate(&predicate.name) {
            for predicate_instance in predicate_state.get_instances() {
                if predicate_instance.inhale_location == location {
                    // We can purify out exhaled predicates.
                    //
                    // FIXME: We also can purify
                    // `PredicateInstanceState::FreshNonAliased`, but purifying
                    // it too early may miss an exhale of the predicate and lead
                    // to an usoudness. (The unsoudness can be replaced with a
                    // verification error by uncommenting the asserts in
                    // `try_removing_predicate_instance`.)
                    if matches!(
                        predicate_instance.state,
                        PredicateInstanceState::Exhaled(_)
                            | PredicateInstanceState::FreshNonAliased
                    ) {
                        return Some(predicate_instance);
                    }
                }
            }
        }
        None
    }

    fn is_purified_exhale(
        &self,
        location: Location,
        predicate: &vir_low::expression::PredicateAccessPredicate,
    ) -> bool {
        if let Some(predicate_state) = self.final_state.get_predicate(&predicate.name) {
            for predicate_instance in predicate_state.get_instances() {
                if let PredicateInstanceState::Exhaled(exhale_location) = predicate_instance.state {
                    if exhale_location == location {
                        assert_eq!(*predicate.permission, predicate_instance.permission_amount);
                        return true;
                    }
                }
            }
        }
        false
    }

    fn save_state(&mut self, label: String) {
        assert!(self
            .predicate_snapshots_at_label
            .insert(label, self.predicate_snapshots.clone())
            .is_none());
    }

    fn purify_snap_calls(
        &mut self,
        expression: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let result = purify_snap_calls(
            &self.predicate_snapshots,
            &self.predicate_snapshots_at_label,
            self.solver,
            self.program,
            expression,
        )?;
        // assert!(check_non_aliased_snap_calls_purified(&result, self.program));
        Ok(result)
    }

    pub(super) fn purify_lifetime_token_inhale(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        self.lifetime_tokens
            .inhale_predicate(&mut self.trace, self.solver, predicate, position)
    }

    pub(super) fn purify_lifetime_token_exhale(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        self.lifetime_tokens
            .exhale_predicate(&mut self.trace, self.solver, predicate, position)
    }

    pub(super) fn try_assert_frac_ref_snapshot_equality(
        &mut self,
        predicate: &vir_low::PredicateAccessPredicate,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<()> {
        let predicate_lifetime = &predicate.arguments[0];
        let predicate_snapshot = &predicate.arguments[4];
        let mut snapshot_candidate = None;
        if let Some(predicate_state) = self.final_state.get_predicate(&predicate.name) {
            for predicate_instance in predicate_state.get_instances() {
                let instance_lifetime = &predicate_instance.arguments[0];
                if self
                    .solver
                    .is_equal(predicate_lifetime, instance_lifetime)?
                {
                    if snapshot_candidate.is_some() {
                        // There are multiple snapshots for the same lifetime.
                        // We cannot assert anything.
                        return Ok(());
                    }
                    snapshot_candidate = Some(&predicate_instance.arguments[4]);
                }
            }
        }
        if let Some(instance_snapshot) = snapshot_candidate {
            self.trace.push(vir_low::Statement::comment(format!(
                "Asserting that the snapshot of {} is equal to the snapshot of the predicate instance",
                predicate.name
            )));
            // This does not work because we do not have accees to the lowerer
            // anymore ☹.
            //
            // ```rust
            // let extensionality_trigger =
            //     self.lowerer.snapshots_extensionality_equal_call(
            //     predicate_snapshot.clone(), instance_snapshot.clone(),
            //     position, )?;
            // ```
            //
            // Instead, we use the following hack.
            let extensionality_trigger = self.program.predicate_snapshots_extensionality_call(
                predicate_snapshot.clone(),
                instance_snapshot.clone(),
                position,
            );
            let extensionality_trigger = purify_snap_calls(
                &self.predicate_snapshots,
                &self.predicate_snapshots_at_label,
                self.solver,
                self.program,
                extensionality_trigger,
            )?;
            assert!(check_non_aliased_snap_calls_purified(
                &extensionality_trigger,
                self.program
            ));
            self.trace
                .push(vir_low::Statement::assert(extensionality_trigger, position));
        }
        Ok(())
    }
}
