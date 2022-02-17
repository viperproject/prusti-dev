//! Module for verifying user-provided specifications after macro expansion

mod common;
mod type_model_checks;
mod predicate_checks;

use common::*;
use type_model_checks::{IllegalModelUsagesChecker, ModelDefinedOnTypeWithoutFields};
use predicate_checks::IllegalPredicateUsagesChecker;
use crate::environment::Environment;

/// Checker visitor for the specifications.
/// Checks are implemented in various [SpecCheckerStrategy]s
pub struct SpecChecker<'tcx> {
    checks: Vec<Box<dyn SpecCheckerStrategy<'tcx>>>,
}

impl<'tcx> Default for SpecChecker<'tcx> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'tcx> SpecChecker<'tcx> {
    pub fn new() -> Self {
        Self {
            checks: vec![
                Box::new(IllegalPredicateUsagesChecker {}),
                Box::new(IllegalModelUsagesChecker {}),
                Box::new(ModelDefinedOnTypeWithoutFields {})
            ]
        }
    }

    /// Executes all checks and emits errors
    pub fn check(&self, env: &Environment<'tcx>) {
        for check in self.checks.iter() {
            let errors = check.check(env);
            for error in errors {
                error.emit(env);
            }
        }
    }
}