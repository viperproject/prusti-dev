use prusti_rustc_interface::hir::intravisit::{
    self,
    Visitor,
};
use prusti_rustc_interface::middle::{
    hir::map::Map,
    ty::TyCtxt,
};
use prusti_rustc_interface::hir::{
    Expr, ExprKind, QPath
};
use prusti_rustc_interface::span::Span;
use prusti_interface::environment::{
    Environment,
    EnvQuery,
};


pub struct CallSpanFinder<'tcx> {
    pub env_query: EnvQuery<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub spans: Vec<(String, Span)>,
}

impl<'tcx> CallSpanFinder<'tcx> {
    pub fn new(env: &Environment<'tcx>) -> Self {
        Self {
            env_query: env.query,
            spans: Vec::new(),
            tcx: env.tcx(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for CallSpanFinder<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.env_query.hir()
    }
    fn visit_expr(&mut self, ex: &'tcx Expr) {
        intravisit::walk_expr(self, ex);
        match ex.kind {
            // Find all calls and methodcalls, not sure what the difference is..
            ExprKind::Call(e1, _e2) => {
                match e1.kind {
                    ExprKind::Path(QPath::Resolved(_ty, path)) => {
                        let defid = path.res.opt_def_id();
                        if defid.is_some() {
                            let defpath = self.tcx.def_path_debug_str(defid.unwrap());
                            self.spans.push((defpath, path.span));
                        }
                    },
                    _ => {},
                }
            },
            ExprKind::MethodCall(path, _e1, _e2, sp) => {
                let ident = format!("{}", path.ident.as_str());
                // let path: &'tcx PathSegment<'tcx> = p;
                let maybe_method_def_id = self
                    .tcx
                    .typeck(ex.hir_id.owner.def_id)
                    .type_dependent_def_id(ex.hir_id);
                if let Some(method_def_id) = maybe_method_def_id {
                    let is_local = method_def_id.as_local().is_some();
                    if !is_local {
                        let defpath = self.tcx.def_path_debug_str(method_def_id);
                        self.spans.push((defpath, sp));
                    }
                }
            },
            ExprKind::Binary(binop, _e1, _e2) | ExprKind::AssignOp(binop, _e1, _e2) => {
                let ident = binop.node.as_str();
                self.spans.push((ident.to_string(), ex.span));
            },
            ExprKind::Unary(unop, _e1) => {
                let ident = unop.as_str();
                self.spans.push((ident.to_string(), ex.span));
            },
            _ => {}
        }
    }
}
