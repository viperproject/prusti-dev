use rustc_hir::intravisit;
use rustc_hir::def_id::DefId;
use rustc_middle::hir::map::Map;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use std::collections::HashMap;

pub struct ExternSpecResolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Map of def id of the real function to the fake function containing the specifications
    extern_fn_map: HashMap<DefId, DefId>,
    current_def_id: Option<DefId>,
}

impl<'tcx> ExternSpecResolver<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
            extern_fn_map: HashMap::new(),
            current_def_id: None,
        }
    }

    pub fn add_extern_fn(&mut self,
                         fn_kind: intravisit::FnKind<'tcx>,
                         fn_decl: &'tcx rustc_hir::FnDecl,
                         body_id: rustc_hir::BodyId,
                         span: Span,
                         id: rustc_hir::hir_id::HirId,) {

        self.current_def_id = Some(self.tcx.hir().local_def_id(id).to_def_id());
        intravisit::Visitor::visit_fn(self, fn_kind, fn_decl, body_id, span, id);
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for ExternSpecResolver<'tcx> {
    type Map = Map<'tcx>;
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        let map = self.tcx.hir();
        intravisit::NestedVisitorMap::All(map)
    }

    fn visit_fn(
        &mut self,
        fn_kind: intravisit::FnKind<'tcx>,
        fn_decl: &'tcx rustc_hir::FnDecl,
        body_id: rustc_hir::BodyId,
        span: Span,
        id: rustc_hir::hir_id::HirId,
    ) {
        intravisit::walk_fn(self, fn_kind, fn_decl, body_id, span, id);
    }

    fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) {
        if let rustc_hir::ExprKind::Call(ref callee_expr, ref arguments) = ex.kind {
            if self.current_def_id.is_some() {
                let def_id = self.tcx.typeck(callee_expr.hir_id.owner).type_dependent_def_id(callee_expr.hir_id);
                assert!(def_id.is_some());
                self.extern_fn_map.insert(def_id.unwrap(), self.current_def_id.take().unwrap());
            }
        }
        intravisit::walk_expr(self, ex);
    }
}


