use crate::environment::Environment;
use log::trace;
use prusti_rustc_interface::{
    hir,
    hir::{
        def_id::DefId,
        intravisit::{walk_expr, Visitor},
    },
    middle::hir::map::Map,
};

use crate::utils::has_spec_only_attr;

pub struct CollectClosureDefsVisitor<'env, 'tcx: 'env> {
    env: &'env Environment<'tcx>,
    map: Map<'tcx>,
    result: Vec<DefId>,
}

impl<'env, 'tcx> CollectClosureDefsVisitor<'env, 'tcx> {
    pub fn new(env: &'env Environment<'tcx>) -> Self {
        CollectClosureDefsVisitor {
            env,
            map: env.query.hir(),
            result: Vec::new(),
        }
    }
    pub fn get_closure_defs(self) -> Vec<DefId> {
        self.result
    }
}

impl<'env, 'tcx> Visitor<'tcx> for CollectClosureDefsVisitor<'env, 'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.map
    }

    #[tracing::instrument(level = "trace", skip(self, expr))]
    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(hir::Closure {
            def_id: local_def_id,
            ..
        }) = expr.kind
        {
            let def_id = local_def_id.to_def_id();
            if !has_spec_only_attr(self.env.query.get_attributes(def_id)) {
                let item_def_path = self.env.name.get_item_def_path(def_id);
                trace!("Add {} to result", item_def_path);
                self.result.push(def_id);
            }
        }

        walk_expr(self, expr)
    }
}
