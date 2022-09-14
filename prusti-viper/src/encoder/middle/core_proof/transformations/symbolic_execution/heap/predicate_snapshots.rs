use crate::encoder::{
    errors::{SpannedEncodingError, SpannedEncodingResult},
    middle::core_proof::transformations::{
        encoder_context::EncoderContext,
        symbolic_execution::{
            egg::EGraphState,
            program_context::ProgramContext,
            utils::{all_heap_independent, arguments_match, is_place_non_aliased},
        },
    },
};
use log::debug;
use std::collections::BTreeMap;
use vir_crate::{
    common::display,
    low::{
        self as vir_low,
        expression::visitors::{ExpressionFallibleFolder, ExpressionWalker},
    },
};

pub(super) fn check_non_aliased_snap_calls_purified<'a>(
    expression: &vir_low::Expression,
    program: &'a ProgramContext<'a, impl EncoderContext>,
) -> bool {
    struct Walker<'a, EC: EncoderContext> {
        program: &'a ProgramContext<'a, EC>,
        found_violation: bool,
    }
    impl<'a, EC: EncoderContext> ExpressionWalker for Walker<'a, EC> {
        fn walk_trigger(&mut self, trigger: &vir_low::Trigger) {
            for term in &trigger.terms {
                self.walk_expression(term);
            }
        }
        fn walk_func_app_enum(&mut self, func_app: &vir_low::expression::FuncApp) {
            self.walk_func_app(func_app);
            let function = self.program.get_function(&func_app.function_name);
            assert_eq!(function.parameters.len(), func_app.arguments.len());
            match function.kind {
                vir_low::FunctionKind::CallerFor => {}
                vir_low::FunctionKind::SnapRange => {}
                vir_low::FunctionKind::MemoryBlockBytes => {}
                vir_low::FunctionKind::Snap => {
                    if is_place_non_aliased(&func_app.arguments[0]) {
                        self.found_violation = true;
                    }
                }
            }
        }
        fn walk_quantifier_enum(&mut self, quantifier: &vir_low::Quantifier) {
            self.walk_quantifier(quantifier);
            if quantifier.body.is_heap_independent() {
                for trigger in &quantifier.triggers {
                    for term in &trigger.terms {
                        assert!(term.is_heap_independent(), "heap dependent trigger: {term}\nin indepedentent quantifier: {quantifier}");
                    }
                }
            }
        }
    }
    let mut purifier = Walker {
        program,
        found_violation: false,
    };
    purifier.walk_expression(expression);
    !purifier.found_violation
}

pub(super) fn purify_snap_calls_vec_with_retry<'a>(
    predicate_snapshots: &'a PredicateSnapshots,
    predicate_snapshots_at_label: &'a BTreeMap<String, PredicateSnapshots>,
    solver: &'a mut EGraphState,
    program: &'a ProgramContext<'a, impl EncoderContext>,
    expressions: Vec<vir_low::Expression>,
) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
    let mut expressions = purify_snap_calls_vec(
        predicate_snapshots,
        predicate_snapshots_at_label,
        solver,
        program,
        expressions,
    )?;
    if !all_heap_independent(&expressions) {
        solver.saturate()?;
        expressions = purify_snap_calls_vec(
            predicate_snapshots,
            predicate_snapshots_at_label,
            solver,
            program,
            expressions,
        )?;
    }
    solver.intern_heap_independent_terms(&expressions)?;
    for expression in &expressions {
        assert!(check_non_aliased_snap_calls_purified(expression, program));
    }
    Ok(expressions)
}

pub(super) fn purify_snap_calls_vec<'a>(
    predicate_snapshots: &'a PredicateSnapshots,
    predicate_snapshots_at_label: &'a BTreeMap<String, PredicateSnapshots>,
    solver: &'a mut EGraphState,
    program: &'a ProgramContext<'a, impl EncoderContext>,
    original_expressions: Vec<vir_low::Expression>,
) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
    let mut expressions = Vec::new();
    for expression in original_expressions {
        expressions.push(purify_snap_calls(
            predicate_snapshots,
            predicate_snapshots_at_label,
            solver,
            program,
            expression,
        )?);
    }
    Ok(expressions)
}

pub(super) fn purify_snap_calls<'a>(
    predicate_snapshots: &'a PredicateSnapshots,
    predicate_snapshots_at_label: &'a BTreeMap<String, PredicateSnapshots>,
    solver: &'a mut EGraphState,
    program: &'a ProgramContext<'a, impl EncoderContext>,
    expression: vir_low::Expression,
) -> SpannedEncodingResult<vir_low::Expression> {
    struct Purifier<'a, EC: EncoderContext> {
        predicate_snapshots: &'a PredicateSnapshots,
        predicate_snapshots_at_label: &'a BTreeMap<String, PredicateSnapshots>,
        solver: &'a mut EGraphState,
        program: &'a ProgramContext<'a, EC>,
        label: Option<String>,
        argument_purified: bool,
    }
    impl<'a, EC: EncoderContext> ExpressionFallibleFolder for Purifier<'a, EC> {
        type Error = SpannedEncodingError;

        fn fallible_fold_trigger(
            &mut self,
            mut trigger: vir_low::Trigger,
        ) -> Result<vir_low::Trigger, Self::Error> {
            for term in std::mem::take(&mut trigger.terms) {
                let new_term = self.fallible_fold_expression(term)?;
                trigger.terms.push(new_term);
            }
            Ok(trigger)
        }

        fn fallible_fold_func_app_enum(
            &mut self,
            func_app: vir_low::expression::FuncApp,
        ) -> Result<vir_low::Expression, Self::Error> {
            let old_argument_purified = self.argument_purified;
            self.argument_purified = false;
            let func_app = self.fallible_fold_func_app(func_app)?;
            if self.argument_purified
                && all_heap_independent(&func_app.arguments)
                && self
                    .solver
                    .intern_heap_independent_terms(&func_app.arguments)?
            {
                self.solver.saturate()?;
            }
            self.argument_purified = old_argument_purified;
            let function = self.program.get_function(&func_app.function_name);
            assert_eq!(function.parameters.len(), func_app.arguments.len());
            match function.kind {
                vir_low::FunctionKind::CallerFor | vir_low::FunctionKind::SnapRange => {
                    Ok(vir_low::Expression::FuncApp(func_app))
                }
                vir_low::FunctionKind::MemoryBlockBytes | vir_low::FunctionKind::Snap => {
                    if let Some(snapshot_variable) =
                        self.resolve_snapshot(&func_app.function_name, &func_app.arguments)?
                    {
                        self.argument_purified = true;
                        Ok(vir_low::Expression::local(
                            snapshot_variable,
                            func_app.position,
                        ))
                    } else {
                        Ok(vir_low::Expression::FuncApp(func_app))
                    }
                }
            }
        }

        fn fallible_fold_labelled_old(
            &mut self,
            mut labelled_old: vir_low::expression::LabelledOld,
        ) -> Result<vir_low::expression::LabelledOld, Self::Error> {
            std::mem::swap(&mut labelled_old.label, &mut self.label);
            labelled_old.base = self.fallible_fold_expression_boxed(labelled_old.base)?;
            std::mem::swap(&mut labelled_old.label, &mut self.label);
            Ok(labelled_old)
        }
    }
    impl<'a, EC: EncoderContext> Purifier<'a, EC> {
        fn resolve_snapshot(
            &mut self,
            function_name: &str,
            arguments: &[vir_low::Expression],
        ) -> SpannedEncodingResult<Option<vir_low::VariableDecl>> {
            let predicate_snapshots = if let Some(label) = &self.label {
                self.predicate_snapshots_at_label.get(label).unwrap()
            } else {
                self.predicate_snapshots
            };
            let Some(predicate_name) = self.program.get_snapshot_predicate(function_name) else {
                // The final snapshot function is already pure and,
                // therefore, is not mapped to a predicate.
                return Ok(None);
            };
            predicate_snapshots.find_snapshot(predicate_name, arguments, self.solver)
        }
    }
    // eprintln!("predicate_snapshots: {predicate_snapshots}");
    let mut purifier = Purifier {
        predicate_snapshots,
        predicate_snapshots_at_label,
        solver,
        program,
        label: None,
        argument_purified: false,
    };
    // eprintln!("expression: {expression}");
    purifier.fallible_fold_expression(expression)
}

#[derive(Default, Clone)]
pub(super) struct PredicateSnapshots {
    snapshots: BTreeMap<String, Vec<PredicateSnapshot>>,
    variables: Vec<vir_low::VariableDecl>,
}

impl std::fmt::Display for PredicateSnapshots {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (predicate_name, snapshots) in &self.snapshots {
            writeln!(f, "Predicate {}", predicate_name)?;
            for snapshot in snapshots {
                writeln!(f, "  {}", snapshot)?;
            }
        }
        Ok(())
    }
}

impl PredicateSnapshots {
    /// Method to be used during the initial symbolic execution.
    pub(super) fn create_non_aliased_predicate_snapshot(
        &mut self,
        program_context: &ProgramContext<impl EncoderContext>,
        predicate_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) -> SpannedEncodingResult<String> {
        let predicate_snapshots = self
            .snapshots
            .entry(predicate_name.to_string())
            .or_default();
        let snapshot_variable_name = format!(
            "snapshot_non_aliased${}$round{}${}",
            predicate_name,
            program_context.get_purification_round(),
            predicate_snapshots.len()
        );
        let snapshot = if let Some(ty) = program_context.get_snapshot_type(predicate_name) {
            let snapshot = vir_low::VariableDecl::new(snapshot_variable_name.clone(), ty);
            self.variables.push(snapshot.clone());
            PredicateSnapshotState::Inhaled(snapshot)
        } else {
            PredicateSnapshotState::NoSnapshot
        };
        assert!(
            all_heap_independent(&arguments),
            "arguments: {}",
            display::cjoin(&arguments)
        );
        predicate_snapshots.push(PredicateSnapshot {
            arguments,
            snapshot,
        });
        Ok(snapshot_variable_name)
    }

    /// Method to be used by the finalizer.
    pub(super) fn register_predicate_snapshot(
        &mut self,
        program_context: &ProgramContext<impl EncoderContext>,
        predicate_name: &str,
        arguments: Vec<vir_low::Expression>,
        snapshot_variable_name: String,
    ) {
        let predicate_snapshots = self
            .snapshots
            .entry(predicate_name.to_string())
            .or_default();
        let snapshot = if let Some(ty) = program_context.get_snapshot_type(predicate_name) {
            let snapshot = vir_low::VariableDecl::new(snapshot_variable_name, ty);
            self.variables.push(snapshot.clone());
            PredicateSnapshotState::Inhaled(snapshot)
        } else {
            PredicateSnapshotState::NoSnapshot
        };
        // assert!(all_heap_independent(&predicate.arguments), "arguments: {}", display::cjoin(&predicate.arguments));
        predicate_snapshots.push(PredicateSnapshot {
            arguments,
            snapshot,
        });
    }

    /// Method to be used by the finalizer.
    pub(super) fn create_predicate_snapshot(
        &mut self,
        program_context: &ProgramContext<impl EncoderContext>,
        predicate_name: &str,
        arguments: Vec<vir_low::Expression>,
    ) {
        let predicate_snapshots = self
            .snapshots
            .entry(predicate_name.to_string())
            .or_default();
        let snapshot_variable_name = format!(
            "snapshot${}$round{}${}",
            predicate_name,
            program_context.get_purification_round(),
            predicate_snapshots.len()
        );
        let snapshot = if let Some(ty) = program_context.get_snapshot_type(predicate_name) {
            let snapshot = vir_low::VariableDecl::new(snapshot_variable_name, ty);
            self.variables.push(snapshot.clone());
            PredicateSnapshotState::Inhaled(snapshot)
        } else {
            PredicateSnapshotState::NoSnapshot
        };
        // assert!(all_heap_independent(&predicate.arguments), "arguments: {}", display::cjoin(&predicate.arguments));
        predicate_snapshots.push(PredicateSnapshot {
            arguments,
            snapshot,
        });
    }

    pub(super) fn destroy_predicate_snapshot(
        &mut self,
        // predicate: &vir_low::expression::PredicateAccessPredicate,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
        solver: &mut EGraphState,
    ) -> SpannedEncodingResult<()> {
        let predicate_snapshots = self
            .snapshots
            .get_mut(predicate_name)
            .unwrap_or_else(|| panic!("no key: {predicate_name} {}", display::cjoin(arguments)));
        for predicate_snapshot in predicate_snapshots.iter_mut() {
            if predicate_snapshot.snapshot.is_not_exhaled()
                && predicate_snapshot.matches_arguments(arguments, solver)?
            {
                predicate_snapshot.snapshot = PredicateSnapshotState::Exhaled;
                return Ok(());
            }
        }
        solver.saturate()?;
        for predicate_snapshot in predicate_snapshots {
            if predicate_snapshot.snapshot.is_not_exhaled()
                && predicate_snapshot.matches_arguments(arguments, solver)?
            {
                predicate_snapshot.snapshot = PredicateSnapshotState::Exhaled;
                return Ok(());
            }
        }
        unreachable!(
            "snapshot not found: {predicate_name} {}",
            display::cjoin(arguments)
        );
    }

    pub(super) fn find_snapshot(
        &self,
        predicate_name: &str,
        arguments: &[vir_low::Expression],
        solver: &EGraphState,
    ) -> SpannedEncodingResult<Option<vir_low::VariableDecl>> {
        if let Some(predicate_snapshots) = self.snapshots.get(predicate_name) {
            for predicate_snapshot in predicate_snapshots {
                if let PredicateSnapshotState::Inhaled(snapshot) = &predicate_snapshot.snapshot {
                    if predicate_snapshot.matches_arguments(arguments, solver)? {
                        return Ok(Some(snapshot.clone()));
                    }
                }
            }
        }
        Ok(None)
    }

    pub(super) fn into_variables(self) -> Vec<vir_low::VariableDecl> {
        self.variables
    }
}

#[derive(Clone, derive_more::Display)]
enum PredicateSnapshotState {
    /// The snapshot is valid.
    Inhaled(vir_low::VariableDecl),
    /// The snapshot was exhaled and no longer valid.
    Exhaled,
    /// The predicate does not have a snapshot.
    NoSnapshot,
}

impl PredicateSnapshotState {
    pub(super) fn is_not_exhaled(&self) -> bool {
        matches!(
            self,
            PredicateSnapshotState::Inhaled(_) | PredicateSnapshotState::NoSnapshot
        )
    }
}

#[derive(Clone)]
pub(super) struct PredicateSnapshot {
    /// Predicate arguments.
    arguments: Vec<vir_low::Expression>,
    /// None means that the corresponding predicate was exhaled.
    snapshot: PredicateSnapshotState,
}

impl std::fmt::Display for PredicateSnapshot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", display::cjoin(&self.arguments), self.snapshot)
    }
}

impl PredicateSnapshot {
    pub(super) fn matches(
        &self,
        predicate: &vir_low::ast::expression::PredicateAccessPredicate,
        solver: &EGraphState,
    ) -> SpannedEncodingResult<bool> {
        arguments_match(&self.arguments, &predicate.arguments, solver)
    }

    pub(super) fn matches_arguments(
        &self,
        arguments: &[vir_low::Expression],
        solver: &EGraphState,
    ) -> SpannedEncodingResult<bool> {
        debug!(
            "matches_arguments:\n  self: {}\n  other: {}",
            display::cjoin(&self.arguments),
            display::cjoin(arguments)
        );
        arguments_match(&self.arguments, arguments, solver)
    }
}
