use super::common::*;
use crate::{
    environment::{EnvQuery, Environment},
    utils::has_prusti_attr,
    PrustiError,
};
use prusti_rustc_interface::{
    hir::{self as hir, intravisit},
    middle::hir::map::Map,
};

/// Declarations of resources or obligations (originating from
/// resource! or obligation!) are illegal inside traits. This
/// checker finds and reports all such illegal declarations.
pub struct ResourceDeclarationChecker;

impl<'tcx> SpecCheckerStrategy<'tcx> for ResourceDeclarationChecker {
    #[tracing::instrument(
        name = "ResourceDeclarationChecker::check",
        level = "debug",
        skip(self, env)
    )]
    fn check(&self, env: &Environment<'tcx>) -> Vec<PrustiError> {
        let mut collector = CollectIllegalDeclarationsVisitor {
            env_query: env.query,
            declaration_errors: Vec::default(),
        };
        env.query.hir().walk_toplevel_module(&mut collector);

        collector.declaration_errors
    }
}

struct CollectIllegalDeclarationsVisitor<'tcx> {
    env_query: EnvQuery<'tcx>,
    declaration_errors: Vec<PrustiError>,
}

impl<'tcx> intravisit::Visitor<'tcx> for CollectIllegalDeclarationsVisitor<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.env_query.hir()
    }

    fn visit_trait_item(&mut self, ti: &'tcx hir::TraitItem<'tcx>) {
        let def_id = ti.owner_id.def_id.to_def_id();
        let attrs = self.env_query.get_local_attributes(ti.owner_id.def_id);

        if has_prusti_attr(attrs, "resource") {
            let error = PrustiError::incorrect(
                "`resource!` declarations are not allowed inside traits",
                self.env_query.get_def_span(def_id).into(),
            );
            self.declaration_errors.push(error);
        } else if has_prusti_attr(attrs, "obligation") {
            let error = PrustiError::incorrect(
                "`obligation!` declarations are not allowed inside traits",
                self.env_query.get_def_span(def_id).into(),
            );
            self.declaration_errors.push(error);
        }

        intravisit::walk_trait_item(self, ti);
    }
}
