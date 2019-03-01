// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::hir;
use syntax::attr;
use rustc::ty::TyCtxt;
use rustc::hir::def_id::DefId;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use std::collections::HashSet;
use std::iter::FromIterator;
use config;
use environment::EnvironmentImpl;

pub struct CollectPrustiSpecVisitor<'r, 'a: 'r, 'tcx: 'a> {
    env: &'r EnvironmentImpl<'r, 'a, 'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    result: &'r mut Vec<DefId>,
    use_whitelist: bool,
    whitelist: HashSet<String>,
}

impl<'r, 'a, 'tcx> CollectPrustiSpecVisitor<'r, 'a, 'tcx> {
    pub fn new(env: &'r EnvironmentImpl<'r, 'a, 'tcx>, result: &'r mut Vec<DefId>) -> Self {
        CollectPrustiSpecVisitor {
            env,
            tcx: env.tcx(),
            result,
            use_whitelist: config::enable_whitelist(),
            whitelist: HashSet::from_iter(config::verification_whitelist())
        }
    }
}

impl<'r, 'a, 'tcx> ItemLikeVisitor<'tcx> for CollectPrustiSpecVisitor<'r, 'a, 'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        if attr::contains_name(&item.attrs, "__PRUSTI_LOOP_SPEC_ID") ||
            attr::contains_name(&item.attrs, "__PRUSTI_EXPR_ID") ||
            attr::contains_name(&item.attrs, "__PRUSTI_FORALL_ID") ||
            attr::contains_name(&item.attrs, "__PRUSTI_SPEC_ONLY") ||
            attr::contains_name(&item.attrs, "trusted") {
                return;
        }
        if let hir::Item_::ItemFn(..) = item.node {
            let def_id = self.tcx.hir.local_def_id(item.id);
            let item_def_path = self.env.get_item_def_path(def_id);
            if !self.use_whitelist || self.whitelist.contains(&item_def_path) {
                trace!("Add {} to result", item_def_path);
                self.result.push(def_id);
            } else {
                debug!("Skip verification of item '{}': not in the whitelist", item_def_path)
            }
        }
    }

    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {
        if attr::contains_name(&trait_item.attrs, "__PRUSTI_SPEC_ONLY") ||
            attr::contains_name(&trait_item.attrs, "trusted") {
            return;
        }
        // Skip body-less trait methods
        if let hir::TraitItemKind::Method(_, hir::TraitMethod::Required(_)) = trait_item.node {
            return;
        }
        let def_id = self.tcx.hir.local_def_id(trait_item.id);
        let item_def_path = self.env.get_item_def_path(def_id);
        if !self.use_whitelist || self.whitelist.contains(&item_def_path) {
            trace!("Add {} to result", item_def_path);
            self.result.push(def_id);
        } else {
            debug!("Skip verification of trait item '{}': not in the whitelist", item_def_path)
        }
    }

    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {
        if attr::contains_name(&impl_item.attrs, "__PRUSTI_SPEC_ONLY") ||
            attr::contains_name(&impl_item.attrs, "trusted") {
            return;
        }
        let def_id = self.tcx.hir.local_def_id(impl_item.id);
        let item_def_path = self.env.get_item_def_path(def_id);
        if !self.use_whitelist || self.whitelist.contains(&item_def_path) {
            trace!("Add {} to result", item_def_path);
            self.result.push(def_id);
        } else {
            debug!("Skip verification of impl item '{}': not in the whitelist", item_def_path)
        }
    }
}
