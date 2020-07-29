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

/// Check whether the `attrs` contain `prusti::$name` attribute.
/// FIXME: Move this function to utils.
pub(crate) fn contains_name(attrs: &[ast::Attribute], name: &str) -> bool {
    for attr in attrs {
        match &attr.kind {
            ast::AttrKind::DocComment(_) => unreachable!(),
            ast::AttrKind::Normal(ast::AttrItem {
                path: ast::Path { span: _, segments },
                args: _,
            }) => {
                if segments.len() == 2 && segments[0].ident.name.with(
                    |attr_name| attr_name == "prusti"
                ) && segments[1].ident.name.with(|attr_name| attr_name == name) {
                    return true;
                }
            }
        }
    }
        false
}

pub struct CollectPrustiSpecVisitor<'a, 'tcx: 'a> {
    env: &'a Environment<'tcx>,
    tcx: TyCtxt<'tcx>,
    result: Vec<DefId>,
    use_whitelist: bool,
    whitelist: HashSet<String>,
}

impl<'a, 'tcx> CollectPrustiSpecVisitor<'a, 'tcx> {
    pub fn new(env: &'a Environment<'tcx>) -> Self {
        CollectPrustiSpecVisitor {
            env,
            tcx: env.tcx(),
            result: Vec::new(),
            use_whitelist: config::enable_whitelist(),
            whitelist: HashSet::from_iter(config::verification_whitelist()),
        }
    }
    pub fn get_annotated_procedures(self) -> Vec<DefId> {
        self.result
    }
}

impl<'a, 'tcx> ItemLikeVisitor<'tcx> for CollectPrustiSpecVisitor<'a, 'tcx> {
    fn visit_item(&mut self, item: &hir::Item) {
        if contains_name(&item.attrs, "spec_only")
        {
            return;
        }
        if let hir::ItemKind::Fn(..) = item.kind {
            let def_id = self.tcx.hir().local_def_id(item.hir_id).to_def_id();
            let item_def_path = self.env.get_item_def_path(def_id);
            trace!("Add {} to result", item_def_path);
            self.result.push(def_id);
        }
    }

    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {
        if contains_name(&trait_item.attrs, "spec_only")
        {
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
        let def_id = self.tcx.hir().local_def_id(trait_item.hir_id).to_def_id();
        let item_def_path = self.env.get_item_def_path(def_id);
        trace!("Add {} to result", item_def_path);
        self.result.push(def_id);
    }

    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {
        if contains_name(&impl_item.attrs, "spec_only")
        {
            return;
        }

        // Skip associated types and other non-methods items
        if let hir::ImplItemKind::Fn(..) = impl_item.kind {
            // continue
        } else {
            return;
        }

        let def_id = self.tcx.hir().local_def_id(impl_item.hir_id).to_def_id();
        let item_def_path = self.env.get_item_def_path(def_id);
        trace!("Add {} to result", item_def_path);
        self.result.push(def_id);
    }
}
