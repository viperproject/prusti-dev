use prusti_rustc_interface::hir::intravisit::{
    self,
    Visitor,
};
use prusti_rustc_interface::middle::hir::map::Map;
use prusti_rustc_interface::hir::{
    Expr, ExprKind,
};
use prusti_rustc_interface::span::Span;
use prusti_interface::environment::{
    Environment,
    EnvQuery,
};


pub struct CallSpanFinder<'tcx> {
    pub env_query: EnvQuery<'tcx>,
    pub spans: Vec<(String, Span)>,
}

impl<'tcx> CallSpanFinder<'tcx> {
    pub fn new(env: &Environment<'tcx>) -> Self {
        Self {
            env_query: env.query,
            spans: Vec::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for CallSpanFinder<'tcx> {
    type Map = Map<'tcx>;
    type NestedFilter = prusti_rustc_interface::middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.env_query.hir()
    }
    fn visit_expr(&mut self, ex: &'tcx Expr) {
        intravisit::walk_expr(self, ex);
        match ex.kind {
            // Find all calls and methodcalls, not sure what the difference is..
            ExprKind::Call(e1, _e2) => {
                // let ident = format!("{}", e1.hir_id); 
                // self.spans.push((ident.clone(), ex.span));
            },
            ExprKind::MethodCall(path, _e1, _e2, _sp) => {
                let ident = format!("{}", path.ident.as_str());
                // let path: &'tcx PathSegment<'tcx> = p;
                
                self.spans.push((ident.clone(), ex.span));
                println!("MethodCall: {:?}", ident);
            },
            _ => {}
        }
    }
}
