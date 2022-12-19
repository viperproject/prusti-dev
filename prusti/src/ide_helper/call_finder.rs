use prusti_rustc_interface::hir::intravisit::{
    self,
    Visitor,
};
use prusti_rustc_interface::middle::{
    hir::map::Map,
    ty::TyCtxt,
};
use prusti_rustc_interface::hir::{
    Expr, ExprKind, QPath,
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
                println!("found a call: resolving!");
                if let ExprKind::Path(ref qself) = e1.kind {
                    let tyck_res = self.tcx.typeck(e1.hir_id.owner.def_id);
                    let res = tyck_res.qpath_res(qself, e1.hir_id);
                    if let prusti_rustc_interface::hir::def::Res::Def(_, def_id) = res {
                        let defpath = self.tcx.def_path_debug_str(def_id);
                        println!("Call DefPath: {}", defpath);
                        self.spans.push((defpath, ex.span))
                    }
                }
            },
            ExprKind::MethodCall(path, e1, _e2, sp) => {
                let ident = format!("Method Call: {}", path.ident.as_str());
                // let path: &'tcx PathSegment<'tcx> = p;
                let maybe_method_def_id = self
                    .tcx
                    .typeck(ex.hir_id.owner.def_id)
                    .type_dependent_def_id(ex.hir_id);
                if let Some(method_def_id) = maybe_method_def_id {
                    let _is_local = method_def_id.as_local().is_some();
                    // if !is_local {
                    let defpath = self.tcx.def_path_debug_str(method_def_id);
                    println!("Found MethodCall: {}", defpath.clone());
                    self.spans.push((defpath, sp));
                // }
                    // try something
                    let owner_def_id = ex.hir_id.owner.def_id;
                    let owner_def_path = self.tcx.def_path_debug_str(owner_def_id.into());
                    // what if we give it e1's defid
                    let tyck_res = self.tcx.typeck(owner_def_id);
                    let substs = tyck_res.node_substs(ex.hir_id);
                    let (other_def_id, _subst) = self
                        .env_query
                        .resolve_method_call(owner_def_id, method_def_id, substs);
                    if other_def_id != method_def_id {
                        let other_def_path = self.tcx.def_path_debug_str(other_def_id);
                        println!("Resolved method call to different defpath: {}", other_def_path);
                        self.spans.push((other_def_path, sp));
                    }
                } // local methods do not need external specifications. 
                // should we still allow it?
                // the interesting thing about methodCalls is that in the case of traits
                // there are 2 possible things we can annotate. The behavior of the trait 
                // methods itself, or the methods of this specific implementation

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

