// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A visitor that collects functions from the HIR

use rustc::hir::itemlikevisit::ItemLikeVisitor;
use rustc::hir::{ImplItem, Item, Item_, TraitItem};
use rustc::ty::TyCtxt;
use syntax::tokenstream::TokenTree;
use syntax::parse::token::{Lit, Token};
use specifications::TypedSpecificationMap;
use specifications::SpecID;

/// HIR visitor
pub struct HirVisitor<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    spec: &'a TypedSpecificationMap,
}

impl<'a, 'tcx: 'a> HirVisitor<'a, 'tcx> {
    /// Builds a new HIR visitor
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, spec: &'a TypedSpecificationMap) -> Self {
        HirVisitor { tcx, spec }
    }

    fn visit_fn(&mut self, item: &'tcx Item) {
        trace!("[visit_fn] enter");

        let attrs = &item.attrs;

        for attr in attrs {
            if attr.path == "__PRUSTI_SPEC" {
                let trees: Vec<TokenTree> = attr.tokens.trees().collect();

                let spec_string = match trees[1] {
                    TokenTree::Token(_, Token::Literal(Lit::StrRaw(ref name, _), None)) => {
                        name.as_str().to_string()
                    }
                    _ => unreachable!(),
                };

                let spec_id: SpecID = spec_string.parse::<u64>().unwrap().into();

                debug!(
                    "HIR item '{}' has spec_id = {}",
                    item.name,
                    spec_id.to_string()
                );

                let spec_set = self.spec.get(&spec_id).unwrap();

                let hir_id = item.hir_id;

                let def_id = self.tcx.hir.local_def_id(item.id);

                let mir = self.tcx.mir_validated(def_id).borrow();

                debug!("spec_id: {:?}", spec_id);
                debug!("hir_id: {:?}", hir_id);
                debug!("def_id: {:?}", def_id);
                debug!("spec_set: '{}...'", &format!("{:?}", spec_set)[..50]);
                debug!("mir: '{}...'", &format!("{:?}", mir)[..50]);

                debug!(
                    "This function has {} local variables. With names:",
                    mir.local_decls.len()
                );
                for local_decl in &mir.local_decls {
                    if let Some(name) = local_decl.name {
                        debug!("- {}: {}", name, local_decl.ty);
                    }
                }
            }
        }

        trace!("[visit_fn] exit");
    }
}

impl<'a, 'tcx: 'a> ItemLikeVisitor<'tcx> for HirVisitor<'a, 'tcx> {
    fn visit_item(&mut self, item: &'tcx Item) {
        trace!("[visit_item] enter");
        if let Item_::ItemFn(..) = item.node {
            self.visit_fn(item)
        }
        trace!("[visit_item] exit");
    }

    fn visit_trait_item(&mut self, _trait_item: &'tcx TraitItem) {}

    fn visit_impl_item(&mut self, _impl_item: &'tcx ImplItem) {}
}
