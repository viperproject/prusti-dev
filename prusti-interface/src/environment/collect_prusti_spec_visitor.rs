// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::config;
use crate::environment::Environment;
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_hir::itemlikevisit::ItemLikeVisitor;
use rustc_middle::ty::TyCtxt;
use std::collections::HashSet;
use std::iter::FromIterator;
use log::{trace, debug};
use rustc_ast::ast;
use crate::utils::{has_spec_only_attr, has_extern_spec_attr};

pub struct CollectPrustiSpecVisitor<'a, 'tcx: 'a> {
    env: &'a Environment<'tcx>,
    tcx: TyCtxt<'tcx>,
    result: Vec<DefId>,
}

impl<'a, 'tcx> CollectPrustiSpecVisitor<'a, 'tcx> {
    pub fn new(env: &'a Environment<'tcx>) -> Self {
        CollectPrustiSpecVisitor {
            env,
            tcx: env.tcx(),
            result: Vec::new(),
        }
    }
    pub fn get_annotated_procedures(self) -> Vec<DefId> {
        self.result
    }
}

impl<'a, 'tcx> ItemLikeVisitor<'tcx> for CollectPrustiSpecVisitor<'a, 'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        let attrs = self.tcx.get_attrs(item.def_id.to_def_id());
        if has_spec_only_attr(attrs) || has_extern_spec_attr(attrs) {
            return;
        }
        if let hir::ItemKind::Fn(..) = item.kind {
            let def_id = self.tcx.hir().local_def_id(item.hir_id()).to_def_id();
            let item_def_path = self.env.get_item_def_path(def_id);
            trace!("Add {} to result", item_def_path);
            self.result.push(def_id);
        }
    }

    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {
        let attrs = self.tcx.get_attrs(trait_item.def_id.to_def_id());
        if has_spec_only_attr(attrs) || has_extern_spec_attr(attrs) {
            return;
        }

        // Skip associated types and other non-methods items
        if let hir::TraitItemKind::Fn(..) = trait_item.kind {
            // continue
        } else {
            return;
        }

        // Skip body-less trait methods
        if let hir::TraitItemKind::Fn(_, hir::TraitFn::Required(_)) = trait_item.kind {
            return;
        }
        let def_id = self.tcx.hir().local_def_id(trait_item.hir_id()).to_def_id();
        let item_def_path = self.env.get_item_def_path(def_id);
        trace!("Add {} to result", item_def_path);
        self.result.push(def_id);
    }

    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {
        let attrs = self.tcx.get_attrs(impl_item.def_id.to_def_id());
        if has_spec_only_attr(attrs) || has_extern_spec_attr(attrs) {
            return;
        }

        // Skip associated types and other non-methods items
        if let hir::ImplItemKind::Fn(..) = impl_item.kind {
            // continue
        } else {
            return;
        }

        let def_id = self.tcx.hir().local_def_id(impl_item.hir_id()).to_def_id();
        let item_def_path = self.env.get_item_def_path(def_id);
        trace!("Add {} to result", item_def_path);
        self.result.push(def_id);
    }

    fn visit_foreign_item(&mut self, _foreign_item: &hir::ForeignItem) {
        // Nothing
    }
}
