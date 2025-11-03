use crate::environment::Environment;
use log::trace;
use prusti_rustc_interface::{
    hir,
    hir::{
        def_id::DefId,
        intravisit::{walk_expr, Visitor},
    },
};

use crate::utils::has_spec_only_attr;

pub struct CollectClosureDefsVisitor<'env, 'tcx: 'env> {
    env: &'env Environment<'tcx>,
    result: Vec<DefId>,
}

impl<'env, 'tcx> CollectClosureDefsVisitor<'env, 'tcx> {
    pub fn new(env: &'env Environment<'tcx>) -> Self {
        CollectClosureDefsVisitor {
            env,
            result: Vec::new(),
        }
    }
    pub fn get_closure_defs(self) -> Vec<DefId> {
        self.result
    }
}

impl<'env, 'tcx> Visitor<'tcx> for CollectClosureDefsVisitor<'env, 'tcx> {
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.env.tcx()
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
                trace!("Add {item_def_path} to result");
                self.result.push(def_id);
            }
        }

        walk_expr(self, expr)
    }
}
