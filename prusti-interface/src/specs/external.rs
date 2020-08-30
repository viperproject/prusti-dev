use rustc_hir::intravisit;
use rustc_hir::def_id::DefId;
use rustc_middle::hir::map::Map;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use std::collections::HashMap;
use crate::specs::typed::ExternSpecificationMap;

pub struct ExternSpecResolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Map of def id of the real function to a tuple containing the def id of the implementing type (or none)
    /// mapped to the fake function with the specifications. Mapped to a tuple to account for trait implementations.
    extern_fn_map: ExternSpecificationMap<'tcx>,
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

    pub fn get_extern_fn_map(&self) -> ExternSpecificationMap<'tcx> {
        self.extern_fn_map.clone()
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
            if self.current_def_id.is_none() {
                intravisit::walk_expr(self, ex);
                return;
            }

            if let rustc_hir::ExprKind::Path(ref qself) = callee_expr.kind {
                let mut impl_ty = None;
                if let rustc_hir::QPath::TypeRelative(ty, _) = qself {
                    if let rustc_hir::TyKind::Path(qpath) = &ty.kind {
                        if let rustc_hir::QPath::Resolved(_, path) = qpath {
                            if let rustc_hir::def::Res::Def(_, id) = path.res {
                                impl_ty = Some(id);
                            }
                        }
                    }
                }

                let res = self.tcx.typeck(callee_expr.hir_id.owner).qpath_res(qself, callee_expr.hir_id);
                if let rustc_hir::def::Res::Def(_, def_id) = res {
                    if self.extern_fn_map.contains_key(&def_id) &&
                            self.extern_fn_map.get(&def_id).unwrap().0 == impl_ty {
                        self.tcx.ty_error_with_message(ex.span.source_callsite(),
                                                       &format!("Duplicate specification for {:?}",
                                                                def_id));
                        self.current_def_id = None;
                    } else {
                        self.extern_fn_map.insert(def_id, (impl_ty, self.current_def_id.take().unwrap()));
                    }
                };
            }
        }
        intravisit::walk_expr(self, ex);
    }
}
