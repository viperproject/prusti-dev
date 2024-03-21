use super::common::*;
use crate::{
    environment::{EnvQuery, Environment},
    utils, PrustiError,
};
use prusti_utils::config;
use prusti_rustc_interface::{ast::ast::Attribute, errors::MultiSpan, hir, middle::hir::map::Map};

/// Checks for mismatched version issues between `prusti` and `prusti-contracts`/`prusti-specs`
pub struct MismatchedVersionsChecker;

impl<'tcx> SpecCheckerStrategy<'tcx> for MismatchedVersionsChecker {
    #[tracing::instrument(
        name = "MismatchedVersionsChecker::check",
        level = "debug",
        skip(self, env)
    )]
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError> {
        let mut check_version = CheckVersionVisitor {
            env_query: env.query,
            errors: Vec::new(),
        };
        env.query.hir().walk_attributes(&mut check_version);

        if let Some(min_prusti_version) = config::min_prusti_version() {
            if env.compare_prusti_version(&min_prusti_version).is_lt() {
                check_version.errors.push(PrustiError::incorrect(
                    format!(
                        "Running Prusti version '{}' when the minimum version required by the \
                        `min_prusti_version` flag of the crate being compiled is '{min_prusti_version}'! \
                        Please update Prusti to version '{min_prusti_version}' or newer.",
                        env.get_prusti_version(),
                    ),
                    MultiSpan::new(),
                ));
            }
        }
        check_version.errors
    }
}

/// Finds all `#[prusti::specs_version = "..."]` attributes and compares them
/// to the version it was compiled with, throwing an error if it was compiled
/// with a higher version.
struct CheckVersionVisitor<'tcx> {
    env_query: EnvQuery<'tcx>,
    errors: Vec<PrustiError>,
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for CheckVersionVisitor<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.env_query.hir()
    }

    fn visit_attribute(&mut self, attr: &'tcx Attribute) {
        // Only report one such error here:
        if !self.errors.is_empty() {
            return;
        }
        if let Some(used_specs_version) = utils::read_specs_version_attr(attr) {
            // If 'compiled with version' > 'version used now for proc-macros' then complain (of `prusti-specs`)
            if Environment::compare_to_curr_specs_version(&used_specs_version).is_gt() {
                let downgrade_msg = config::min_prusti_version()
                    .map(|prusti_ver| format!(" Alternatively you could downgrade your Prusti version to '{prusti_ver}'."))
                    .unwrap_or_default();
                self.errors.push(PrustiError::incorrect(
                    format!(
                        "The version of `prusti-specs` used is '{used_specs_version}', however your Prusti executable was \
                        built with '{0}'! Please use `prusti-specs` version '{0}' or newer.{downgrade_msg}",
                        Environment::get_specs_version(),
                    ),
                    MultiSpan::from_span(attr.span),
                ));
            }
        }
    }
}
