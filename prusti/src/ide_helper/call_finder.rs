use prusti_interface::environment::{EnvQuery, Environment};
use prusti_rustc_interface::{
    hir::{
        def_id::DefId,
        intravisit::{self, Visitor},
        Expr, ExprKind,
    },
    middle::{hir::map::Map, ty::TyCtxt},
    span::Span,
};

/// The hir-visitor to collect all the function calls
pub struct CallSpanFinder<'tcx> {
    pub env_query: EnvQuery<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub called_functions: Vec<(String, DefId, Span)>,
}

impl<'tcx> CallSpanFinder<'tcx> {
    pub fn new(env: &Environment<'tcx>) -> Self {
        Self {
            env_query: env.query,
            called_functions: Vec::new(),
            tcx: env.tcx(),
        }
    }

    pub fn resolve_expression(&self, expr: &'tcx Expr) -> Result<(DefId, DefId), ()> {
        let maybe_method_def_id = self
            .tcx
            .typeck(expr.hir_id.owner.def_id)
            .type_dependent_def_id(expr.hir_id);
        if let Some(method_def_id) = maybe_method_def_id {
            let owner_def_id = expr.hir_id.owner.def_id;
            let tyck_res = self.tcx.typeck(owner_def_id);
            let substs = tyck_res.node_substs(expr.hir_id);
            let (resolved_def_id, _subst) =
                self.env_query
                    .resolve_method_call(owner_def_id, method_def_id, substs);
            Ok((method_def_id, resolved_def_id))
        } else {
            Err(())
        }
    }
}

impl<'tcx> Visitor<'tcx> for CallSpanFinder<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.env_query.hir()
    }
    fn visit_expr(&mut self, expr: &'tcx Expr) {
        intravisit::walk_expr(self, expr);
        match expr.kind {
            ExprKind::Call(e1, _e2) => {
                if let ExprKind::Path(ref qself) = e1.kind {
                    let tyck_res = self.tcx.typeck(e1.hir_id.owner.def_id);
                    let res = tyck_res.qpath_res(qself, e1.hir_id);
                    if let prusti_rustc_interface::hir::def::Res::Def(_, def_id) = res {
                        if def_id.as_local().is_none() {
                            let defpath = self.tcx.def_path_str(def_id);
                            self.called_functions.push((defpath, def_id, expr.span));
                        }
                    }
                }
            }
            ExprKind::MethodCall(_path, _e1, _e2, sp) => {
                let resolve_res = self.resolve_expression(expr);
                if let Ok((method_def_id, resolved_def_id)) = resolve_res {
                    let defpath_unresolved = self.tcx.def_path_str(method_def_id);
                    let defpath_resolved = self.tcx.def_path_str(resolved_def_id);

                    if method_def_id.as_local().is_none() {
                        if defpath_unresolved == defpath_resolved {
                            self.called_functions
                                .push((defpath_resolved, resolved_def_id, sp));
                        } else {
                            // in this case we want both
                            self.called_functions
                                .push((defpath_resolved, resolved_def_id, sp));
                            self.called_functions
                                .push((defpath_unresolved, method_def_id, sp));
                        }
                    }
                }
            }
            ExprKind::Binary(..) | ExprKind::AssignOp(..) | ExprKind::Unary(..) => {
                let resolve_res = self.resolve_expression(expr);
                // this will already fail for standard addition
                if let Ok((method_def_id, resolved_def_id)) = resolve_res {
                    let defpath_unresolved = self.tcx.def_path_str(method_def_id);
                    let defpath_resolved = self.tcx.def_path_str(resolved_def_id);

                    if method_def_id.as_local().is_none() {
                        if defpath_unresolved == defpath_resolved {
                            self.called_functions.push((
                                defpath_resolved,
                                resolved_def_id,
                                expr.span,
                            ));
                        } else {
                            // For binary operations this will be the operation
                            // from the standard libary and the "overriding" method

                            self.called_functions.push((
                                defpath_resolved,
                                resolved_def_id,
                                expr.span,
                            ));
                            self.called_functions.push((
                                defpath_unresolved,
                                method_def_id,
                                expr.span,
                            ));
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
