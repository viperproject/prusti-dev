//! Module for verifying user-provided specifications after macro expansion

mod common;
mod predicate_checks;
mod type_model_checks;
mod version_checks;

use crate::environment::Environment;
use common::*;
use predicate_checks::IllegalPredicateUsagesChecker;
use type_model_checks::{IllegalModelUsagesChecker, ModelDefinedOnTypeWithoutFields};
use version_checks::MismatchedVersionsChecker;

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
                Box::new(MismatchedVersionsChecker {}),
                Box::new(IllegalPredicateUsagesChecker {}),
                Box::new(IllegalModelUsagesChecker {}),
                Box::new(ModelDefinedOnTypeWithoutFields {}),
            ],
        }
    }

    /// Executes all checks and emits errors
    #[tracing::instrument(name = "SpecChecker::check", level = "debug", skip(self, env))]
    pub fn check(&self, env: &Environment<'tcx>) {
        for check in self.checks.iter() {
            let errors = check.check(env);
            for error in errors {
                error.emit(&env.diagnostic);
            }
        }
    }
}
