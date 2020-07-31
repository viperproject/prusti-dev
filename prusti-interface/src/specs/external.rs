use rustc_hir::intravisit;
use rustc_middle::hir::map::Map;
use rustc_middle::ty::TyCtxt;

use std::collections::HashSet;

pub struct ExternSpecResolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    krates: HashSet<rustc_hir::def_id::CrateNum>,
}

impl<'tcx> ExternSpecResolver<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
            krates: HashSet::new(),
        }
    }

    pub fn collect_extern_crates(&mut self) {
        for k_num in self.tcx.all_crate_nums(rustc_hir::def_id::LOCAL_CRATE) {
            println!("Crate name: {:?}", self.tcx.original_crate_name(*k_num));
            if true { // TODO: If external spec for crate exists
                self.krates.insert(*k_num);
            }
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for ExternSpecResolver<'tcx> {
    type Map = Map<'tcx>;
    fn nested_visit_map<'this>(&'this mut self) -> intravisit::NestedVisitorMap<Self::Map> {
        let map = self.tcx.hir();
        intravisit::NestedVisitorMap::All(map)
    }
    fn visit_expr(&mut self, ex: &'tcx rustc_hir::Expr<'tcx>) {
        match ex.kind {
            rustc_hir::ExprKind::Call(ref callee_expression, ref arguments) => {
                // TODO
            }
            rustc_hir::ExprKind::MethodCall(ref segment, _, arguments, _) => {

                let def_id = self.tcx.typeck(ex.hir_id.owner).type_dependent_def_id(ex.hir_id);
                println!("Callee Def Id: {:?}", def_id);
                println!("Original Crate Name: {:?}", self.tcx.original_crate_name(def_id.unwrap().krate));
                println!("Typeof: {:?}", self.tcx.type_of(def_id.unwrap()));
                println!("Path str: {:?}", self.tcx.def_path_str(def_id.unwrap()));

            }
            _ => {}
        }
        intravisit::walk_expr(self, ex);
    }
}


