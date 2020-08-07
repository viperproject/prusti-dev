use rustc_hir::intravisit;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::hir::map::Map;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use std::collections::HashSet;
use std::collections::HashMap;

type CrateSymbol = rustc_span::symbol::Symbol;
type FnInfoMap = HashMap<rustc_span::symbol::Symbol, Vec<FnInfo>>;

struct FnInfo {
    def_id: LocalDefId,
    path: Vec<i32>
}

pub struct ExternSpecResolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    krates: HashMap<CrateSymbol, FnInfoMap>,
}

impl<'tcx> ExternSpecResolver<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let mut krates: HashMap<CrateSymbol, FnInfoMap> = HashMap::new();
        for k_num in tcx.all_crate_nums(rustc_hir::def_id::LOCAL_CRATE) {
            let k_sym = tcx.original_crate_name(*k_num);
            krates.insert(k_sym, HashMap::new());
        }
        Self {
            tcx: tcx,
            krates: krates,
        }
    }

    pub fn add_extern_fn(&mut self,
                         fn_kind: intravisit::FnKind<'tcx>,
                         fn_decl: &'tcx rustc_hir::FnDecl,
                         body_id: rustc_hir::BodyId,
                         span: Span,
                         id: rustc_hir::hir_id::HirId,) {

        // let node = self.tcx.hir().get(body_id.hir_id);
        // println!();
        // println!("{:?}", node);
        // println!();
        intravisit::Visitor::visit_fn(self, fn_kind, fn_decl, body_id, span, id);

        let local_id = self.tcx.hir().local_def_id(id);
        // self.tcx.hir().
        // let p: syn::Path = syn::parse_str(&path).unwrap();
        // let krate: CrateSymbol = CrateSymbol::intern(&p.segments[0].ident.to_string());
        // if self.krates.get(&krate).is_none() {
        //     return;
        // }

        // let info = FnInfo {
        //     def_id: local_id, //.to_def_id()
        //     path: Vec::new()
        // };

        // println!("Path: {:?}", self.tcx.hir().def_path(def_id.unwrap()));
        // println!("path: {:?}", p);
        // println!("ident: {:?}", p.segments[0].ident);
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
        match ex.kind {
            rustc_hir::ExprKind::Call(ref callee_expr, ref arguments) => {
                let def_id = self.tcx.typeck(callee_expr.hir_id.owner).type_dependent_def_id(callee_expr.hir_id);
                println!("Callee Def Id: {:?}", def_id);
            }
            rustc_hir::ExprKind::MethodCall(ref segment, _, arguments, _) => {

                let def_id = self.tcx.typeck(ex.hir_id.owner).type_dependent_def_id(ex.hir_id);

                println!("Callee Def Id: {:?}", def_id);
                println!("Original Crate Name: {:?}", self.tcx.original_crate_name(def_id.unwrap().krate));
                println!("Typeof: {:?}", self.tcx.type_of(def_id.unwrap()));
                println!("Kind: {:?}", self.tcx.type_of(def_id.unwrap()).kind);
                println!("Path str: {:?}", self.tcx.def_path_str(def_id.unwrap()));
                println!("Path: {:?}", self.tcx.def_path(def_id.unwrap()));
            }
            rustc_hir::ExprKind::Path(ref qpath) => {
                // println!();
                // println!("{:?}", qpath);
                match *qpath {
                    rustc_hir::QPath::Resolved(ref maybe_qself, ref path) => {}
                    rustc_hir::QPath::TypeRelative(ref qself, ref segment) => {

                        if let rustc_hir::TyKind::Path(ref qpath) = qself.kind {
                            if let rustc_hir::QPath::Resolved(_, ref path) = qpath {
                                if let rustc_hir::def::Res::Def(_, ref def_id) = path.res {
                                    // println!("path: {:?}", def_id);
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, ex);
    }
}


