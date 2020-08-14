use rustc_hir::intravisit::{Visitor, NestedVisitorMap, ErasedMap, walk_expr};
use rustc_hir as hir;
use rustc_middle::hir::map::Map;
use crate::environment::collect_prusti_spec_visitor::contains_name;

pub struct CollectClosureDefsVisitor<'tcx> {
    map: Map<'tcx>,
    result: Vec<hir::HirId>
}

impl<'tcx> CollectClosureDefsVisitor<'tcx> {
    pub fn new(map: Map<'tcx>) -> Self {
        CollectClosureDefsVisitor {
            map: map,
            result: Vec::new(),
        }
    }
    pub fn get_closure_defs(self) -> Vec<hir::HirId> {
        self.result
    }
}

impl<'tcx> Visitor<'tcx> for CollectClosureDefsVisitor<'tcx> {
    type Map = Map<'tcx>;

    fn nested_visit_map(&mut self) -> NestedVisitorMap<Self::Map> {
        NestedVisitorMap::OnlyBodies (self.map)
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        match expr.kind {
            hir::ExprKind::Closure(_, _, _, _, _) => {
                if !contains_name(&expr.attrs, "spec_only") {
                    self.result.push(expr.hir_id);
                }
            },

            _ => {},
        }

        walk_expr (self, expr)
    }
}
