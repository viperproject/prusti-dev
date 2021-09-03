use rustc_hir::intravisit::{Visitor, NestedVisitorMap, ErasedMap, walk_expr, FnKind};
use rustc_hir as hir;
use rustc_middle::hir::map::Map;
use crate::environment::Environment;
use log::{trace, debug};
use rustc_hir::def_id::DefId;
use rustc_span::Span;
use rustc_middle::ty::TypeckResults;
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
            map: env.tcx().hir(),
            result: Vec::new(),
        }
    }
    pub fn get_closure_defs(self) -> Vec<DefId> {
        self.result
    }
}

impl<'env, 'tcx> Visitor<'tcx> for CollectClosureDefsVisitor<'env, 'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::OnlyBodies (self.map)
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(_, _, _, _, _) = expr.kind {
            if !has_spec_only_attr(self.map.attrs(expr.hir_id)) {
                let _tcx = self.env.tcx();
                let def_id = self.map.local_def_id(expr.hir_id).to_def_id();
                let item_def_path = self.env.get_item_def_path(def_id);
                trace!("Add {} to result", item_def_path);
                self.result.push(def_id);
            }
        }

        walk_expr (self, expr)
    }
}
