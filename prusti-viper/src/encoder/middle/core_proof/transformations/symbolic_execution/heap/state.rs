use super::{
    predicate_snapshots::{
        purify_snap_calls, purify_snap_calls_vec_with_retry, PredicateSnapshots,
    },
    Location,
};
use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution::{
            egg::EGraphState,
            program_context::ProgramContext,
            utils::{all_heap_independent, arguments_match, is_place_non_aliased},
        },
    },
};
use std::collections::BTreeMap;
use vir_crate::{
    common::display,
    low::{self as vir_low},
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum PurificationResult {
    Success,
    Error(vir_low::Position),
}

#[derive(Default, Clone)]
pub(in super::super) struct HeapState {
    /// A map from predicate names to their state.
    predicates: BTreeMap<String, PredicateState>,
    predicate_snapshots: PredicateSnapshots,
    predicate_snapshots_at_label: BTreeMap<String, PredicateSnapshots>,
}

impl std::fmt::Display for HeapState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (predicate_name, predicate_state) in &self.predicates {
            writeln!(f, "{predicate_name}:")?;
            for predicate_instance in &predicate_state.instances {
                writeln!(
                    f,
                    "  {} @ {:?}: {}, {:?}",
                    display::cjoin(&predicate_instance.arguments),
                    predicate_instance.inhale_location,
                    predicate_instance.permission_amount,
                    predicate_instance.state
                )?;
            }
        }
        writeln!(
            f,
            "current predicate snapshots:\n{}",
            self.predicate_snapshots
        )?;
        Ok(())
    }
}

impl HeapState {
    fn is_predicate_instance_non_aliased(
        &mut self,
        solver: &mut EGraphState,
        program: &ProgramContext<impl EncoderContext>,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
    ) -> SpannedEncodingResult<bool> {
        if program.is_predicate_kind_non_aliased(predicate_name) {
            return Ok(true);
        }
        fn construct_predicate_address_non_aliased_call(
            predicate_address: &vir_low::Expression,
        ) -> vir_low::Expression {
            use vir_low::macros::*;
            let address_is_non_aliased = ty!(Bool);
            expr! {
                (ComputeAddress::address_is_non_aliased([predicate_address.clone()]))
            }
        }
        match program.get_predicate_kind(predicate_name) {
            vir_low::PredicateKind::MemoryBlock => {
                let predicate_address = &arguments[0];
                let predicate_address_non_aliased_call =
                    construct_predicate_address_non_aliased_call(predicate_address);
                solver.intern_term(&predicate_address_non_aliased_call)?;
                if solver.is_true(&predicate_address_non_aliased_call)? {
                    return Ok(true);
                } else {
                    solver.saturate()?;
                    if solver.is_true(&predicate_address_non_aliased_call)? {
                        return Ok(true);
                    }
                }
            }
            vir_low::PredicateKind::Owned => {
                let predicate_place = &arguments[0];
                if is_place_non_aliased(predicate_place) {
                    return Ok(true);
                }
            }
            _ => {}
        }
        Ok(false)
    }

    pub(in super::super) fn purify_expression_with_retry(
        &mut self,
        solver: &mut EGraphState,
        program: &ProgramContext<impl EncoderContext>,
        expression: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut expression = purify_snap_calls(
            &self.predicate_snapshots,
            &self.predicate_snapshots_at_label,
            solver,
            program,
            expression,
        )?;
        if !expression.is_heap_independent() {
            solver.saturate()?;
            expression = purify_snap_calls(
                &self.predicate_snapshots,
                &self.predicate_snapshots_at_label,
                solver,
                program,
                expression,
            )?;
        }
        Ok(expression)
    }

    fn purify_predicate_arguments_with_retry(
        &mut self,
        solver: &mut EGraphState,
        program: &ProgramContext<impl EncoderContext>,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        purify_snap_calls_vec_with_retry(
            &self.predicate_snapshots,
            &self.predicate_snapshots_at_label,
            solver,
            program,
            arguments,
        )
        // eprintln!("purify_predicate_arguments_with_retry");
        // eprintln!("  1: {}", display::cjoin(&arguments));
        // let mut arguments = purify_snap_calls_vec(
        //     &self.predicate_snapshots,
        //     &self.predicate_snapshots_at_label,
        //     solver,
        //     program,
        //     arguments,
        // )?;
        // eprintln!("  2: {}", display::cjoin(&arguments));
        // if !all_heap_independent(&arguments) {
        //     solver.saturate()?;
        //     arguments = purify_snap_calls_vec(
        //         &self.predicate_snapshots,
        //         &self.predicate_snapshots_at_label,
        //         solver,
        //         program,
        //         arguments,
        //     )?;
        //     eprintln!("  3: {}", display::cjoin(&arguments));
        // }
        // eprintln!("  4: {}", display::cjoin(&arguments));
        // solver.intern_heap_independent_terms(&arguments)?;
        // Ok(arguments)
    }

    pub(super) fn save_state(&mut self, label: String) {
        assert!(self
            .predicate_snapshots_at_label
            .insert(label, self.predicate_snapshots.clone())
            .is_none());
    }

    pub(super) fn add_predicate_instance(
        &mut self,
        solver: &mut EGraphState,
        program: &ProgramContext<impl EncoderContext>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        inhale_location: Location,
    ) -> SpannedEncodingResult<()> {
        let arguments = self.purify_predicate_arguments_with_retry(
            solver,
            program,
            predicate.arguments.clone(),
        )?;
        let (state, snapshot) = if all_heap_independent(&arguments) {
            if self.is_predicate_instance_non_aliased(
                solver,
                program,
                &predicate.name,
                &arguments,
            )? {
                let predicate_snapshot = self
                    .predicate_snapshots
                    .create_non_aliased_predicate_snapshot(
                        program,
                        &predicate.name,
                        arguments.clone(),
                    )?;
                (
                    PredicateInstanceState::FreshNonAliased,
                    Some(predicate_snapshot),
                )
            } else {
                (PredicateInstanceState::FreshAliased, None)
            }
        } else {
            self.mark_predicate_instances_seen_qp_inhale(&predicate.name);
            (PredicateInstanceState::FreshHeapDependent, None)
        };
        let predicate_name = predicate.name.clone();
        let predicate_state =
            self.predicates
                .entry(predicate_name)
                .or_insert_with(|| PredicateState {
                    instances: Vec::new(),
                });
        let predicate_instance = PredicateInstance {
            arguments,
            permission_amount: (*predicate.permission).clone(),
            inhale_location,
            state,
            snapshot,
        };
        predicate_state.instances.push(predicate_instance);
        Ok(())
    }

    pub(super) fn try_removing_predicate_instance(
        &mut self,
        solver: &mut EGraphState,
        program: &mut ProgramContext<impl EncoderContext>,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        exhale_location: Location,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<PurificationResult> {
        let arguments = self.purify_predicate_arguments_with_retry(
            solver,
            program,
            predicate.arguments.clone(),
        )?;
        if all_heap_independent(&arguments) {
            let is_instance_non_aliased = self.is_predicate_instance_non_aliased(
                solver,
                program,
                &predicate.name,
                &arguments,
            )?;
            if let Some(predicate_state) = self.predicates.get_mut(&predicate.name) {
                for predicate_instance in &mut predicate_state.instances {
                    // eprintln!("predicate_instance {} state: {:?}", display::cjoin(&predicate_instance.arguments), predicate_instance.state);
                    if matches!(
                        predicate_instance.state,
                        PredicateInstanceState::FreshAliased
                            | PredicateInstanceState::FreshNonAliased
                            | PredicateInstanceState::SeenQPExhale
                    ) && predicate_instance.matches(&arguments, &predicate.permission, solver)?
                    {
                        predicate_instance.state = PredicateInstanceState::Exhaled(exhale_location);
                        assert_eq!(predicate_instance.permission_amount, *predicate.permission);
                        if predicate_instance.snapshot.is_some() {
                            self.predicate_snapshots.destroy_predicate_snapshot(
                                &predicate.name,
                                &arguments,
                                solver,
                            )?;
                        }
                        return Ok(PurificationResult::Success);
                    }
                }
                if is_instance_non_aliased {
                    // Report the failure to the caller so that they mark the
                    // state as unreachable.
                    let new_position = program
                        .env()
                        .change_error_context(position, ErrorCtxt::ExhaleNonAliasedPredicate);
                    return Ok(PurificationResult::Error(new_position));
                    // let span = program.env().get_span(position).unwrap();
                    // error_incorrect!(span =>
                    //     "there might be insufficient permission to a place"
                    // )
                }
                assert!(
                    !is_instance_non_aliased,
                    "Failed to exhale non-aliased predicate: {predicate}"
                );
                // Failed to exhale, mark all instances as failed exhale.
                for predicate_instance in &mut predicate_state.instances {
                    if matches!(
                        predicate_instance.state,
                        PredicateInstanceState::FreshAliased | PredicateInstanceState::SeenQPExhale
                    ) {
                        predicate_instance.state = PredicateInstanceState::SeenFailedExhale;
                    }
                }
            } else if is_instance_non_aliased {
                // Report the failure to the caller so that they mark the
                // state as unreachable.
                let new_position = program
                    .env()
                    .change_error_context(position, ErrorCtxt::UnexpectedUnreachable);
                return Ok(PurificationResult::Error(new_position));
            }
        } else {
            self.mark_predicate_instances_seen_qp_exhale(&predicate.name);
        }
        Ok(PurificationResult::Success)
    }

    pub(super) fn mark_predicate_instances_seen_qp_inhale(&mut self, predicate_name: &str) {
        if let Some(predicate_state) = self.predicates.get_mut(predicate_name) {
            for predicate_instance in &mut predicate_state.instances {
                if predicate_instance.state == PredicateInstanceState::SeenQPExhale {
                    predicate_instance.state = PredicateInstanceState::SeenQPInhale;
                }
            }
        }
    }

    pub(super) fn mark_predicate_instances_seen_qp_exhale(&mut self, predicate_name: &str) {
        if let Some(predicate_state) = self.predicates.get_mut(predicate_name) {
            for predicate_instance in &mut predicate_state.instances {
                if predicate_instance.state == PredicateInstanceState::FreshAliased {
                    predicate_instance.state = PredicateInstanceState::SeenQPExhale;
                }
            }
        }
    }

    pub(super) fn get_predicate(&self, predicate_name: &str) -> Option<&PredicateState> {
        self.predicates.get(predicate_name)
    }
}

#[derive(Clone)]
pub(super) struct PredicateState {
    instances: Vec<PredicateInstance>,
}

impl PredicateState {
    pub(super) fn get_instances(&self) -> &[PredicateInstance] {
        &self.instances
    }
}

#[derive(Clone)]
pub(super) struct PredicateInstance {
    /// The arguments of the predicate instance.
    pub(super) arguments: Vec<vir_low::Expression>,
    pub(super) permission_amount: vir_low::Expression,
    /// The location of the inhale statement that inhaled this predicate instance.
    pub(super) inhale_location: Location,
    /// The state of the predicate.
    pub(super) state: PredicateInstanceState,
    /// The snapshot variable name given when purifying a non-aliased predicate.
    pub(super) snapshot: Option<String>,
}

impl PredicateInstance {
    fn matches(
        &self,
        predicate_arguments: &[vir_low::Expression],
        permission: &vir_low::Expression,
        solver: &EGraphState,
    ) -> SpannedEncodingResult<bool> {
        assert_eq!(self.arguments.len(), predicate_arguments.len());
        if !arguments_match(&self.arguments, predicate_arguments, solver)? {
            return Ok(false);
        }
        Ok(self.permission_amount == *permission)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(super) enum PredicateInstanceState {
    /// The predicate was inhaled and has not seen QP exhale yet. The predicate
    /// instance can be aliased by QPs, etc.
    FreshAliased,
    /// The predicate was inhaled. The predicate instance cannot be aliased by
    /// QPs.
    FreshNonAliased,
    SeenQPExhale,
    SeenQPInhale,
    SeenFailedExhale,
    Exhaled(Location),
    FreshHeapDependent,
}
