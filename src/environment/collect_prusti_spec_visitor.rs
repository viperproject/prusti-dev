// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::hir;
use syntax::attr;
use rustc::ty::{self, Ty, TyCtxt};
use rustc::hir::def_id::DefId;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use constants::PRUSTI_SPEC_ATTR;

pub struct CollectPrustiSpecVisitor<'a, 'tcx: 'a, 'gcx: 'tcx > {
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    result: &'a mut Vec<DefId>,
}

impl<'a, 'tcx, 'gcx> CollectPrustiSpecVisitor<'a, 'tcx, 'gcx> {
    pub fn new(tcx: TyCtxt<'a, 'gcx, 'tcx>, result: &'a mut Vec<DefId>) -> Self {
        CollectPrustiSpecVisitor {
            tcx,
            result: result
        }
    }
}

impl<'a, 'gcx, 'tcx> ItemLikeVisitor<'tcx> for CollectPrustiSpecVisitor<'a, 'gcx, 'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        if attr::contains_name(&item.attrs, PRUSTI_SPEC_ATTR) {
            let def_id = self.tcx.hir.local_def_id(item.id);
            self.result.push(def_id);
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &hir::TraitItem) {}

    fn visit_impl_item(&mut self, _impl_item: &hir::ImplItem) {}
}
