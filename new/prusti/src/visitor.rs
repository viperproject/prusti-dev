use rustc_hir::itemlikevisit::ItemLikeVisitor;
use rustc_middle::ty::TyCtxt;

/// A visitor that just prints information about HIR types.
pub struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> HirVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }
}

impl<'hir, 'tcx: 'hir> ItemLikeVisitor<'hir> for HirVisitor<'tcx> {
    fn visit_item(&mut self, item: &'hir rustc_hir::Item<'hir>) {
        println!("HIR Item: {}", item.ident);
        let def_path = self.tcx.hir().opt_local_def_id(item.hir_id).unwrap();
        match &item.kind {
            rustc_hir::ItemKind::Fn(_sig, _generics, _body_id) => {
                let mir = self.tcx.optimized_mir(def_path);
                println!("  Return type is unit: {}", mir.return_ty().is_unit());
            }
            _ => {
                println!("  Not a function");
            }
        }
    }
    fn visit_trait_item(&mut self, trait_item: &'hir rustc_hir::TraitItem<'hir>) {
        println!("HIR Item: {}", trait_item.ident);
    }
    fn visit_impl_item(&mut self, impl_item: &'hir rustc_hir::ImplItem<'hir>) {
        println!("HIR Item: {}", impl_item.ident);
    }
}
