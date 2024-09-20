// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{EnvName, EnvQuery};
use crate::{
    environment::Environment,
    utils::{has_extern_spec_attr, has_spec_only_attr},
};
use log::trace;
use prusti_rustc_interface::{
    hir,
    hir::{def_id::DefId, intravisit::Visitor},
    middle::ty::{self, TyKind},
};

pub struct CollectPrustiSpecVisitor<'tcx> {
    env_query: EnvQuery<'tcx>,
    env_name: EnvName<'tcx>,
    procedures: Vec<DefId>,
    types: Vec<ty::Ty<'tcx>>,
}

impl<'tcx> CollectPrustiSpecVisitor<'tcx> {
    pub fn new(env: &Environment<'tcx>) -> Self {
        CollectPrustiSpecVisitor {
            env_query: env.query,
            env_name: env.name,
            procedures: Vec::new(),
            types: Vec::new(),
        }
    }

    pub fn into_result(self) -> (Vec<DefId>, Vec<ty::Ty<'tcx>>) {
        (self.procedures, self.types)
    }

    pub fn visit_all_item_likes(&mut self) {
        let items = self.env_query.tcx().hir_crate_items(());
        for id in items.free_items() {
            self.visit_item(self.env_query.hir().item(id));
        }
        for id in items.trait_items() {
            self.visit_trait_item(self.env_query.hir().trait_item(id));
        }
        for id in items.impl_items() {
            self.visit_impl_item(self.env_query.hir().impl_item(id));
        }
        for id in items.foreign_items() {
            self.visit_foreign_item(self.env_query.hir().foreign_item(id));
        }
    }
}

impl<'tcx> Visitor<'tcx> for CollectPrustiSpecVisitor<'tcx> {
    #[tracing::instrument(level = "trace", skip(self, item))]
    fn visit_item(&mut self, item: &hir::Item) {
        let attrs = self.env_query.get_local_attributes(item.owner_id.def_id);
        if has_spec_only_attr(attrs) || has_extern_spec_attr(attrs) {
            return;
        }
        if let hir::ItemKind::Fn(..) = item.kind {
            let def_id = self.env_query.as_local_def_id(item.hir_id()).to_def_id();
            let item_def_path = self.env_name.get_item_def_path(def_id);
            trace!("Add {} to procedures", item_def_path);
            self.procedures.push(def_id);
        }
        if matches!(
            item.kind,
            hir::ItemKind::Enum(..) | hir::ItemKind::Struct(..) | hir::ItemKind::Union(..)
        ) {
            let def_id = self.env_query.as_local_def_id(item.hir_id()).to_def_id();
            let adt_def = self.env_query.tcx().adt_def(def_id);
            let ty = self
                .env_query
                .tcx()
                .mk_ty_from_kind(TyKind::Adt(adt_def, self.env_query.identity_substs(def_id)));
            self.types.push(ty);
        }
    }

    #[tracing::instrument(level = "trace", skip(self, trait_item))]
    fn visit_trait_item(&mut self, trait_item: &hir::TraitItem) {
        let attrs = self
            .env_query
            .get_local_attributes(trait_item.owner_id.def_id);
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
        let def_id = self
            .env_query
            .as_local_def_id(trait_item.hir_id())
            .to_def_id();
        let item_def_path = self.env_name.get_item_def_path(def_id);
        trace!("Add {} to procedures", item_def_path);
        self.procedures.push(def_id);
    }

    #[tracing::instrument(level = "trace", skip(self, impl_item))]
    fn visit_impl_item(&mut self, impl_item: &hir::ImplItem) {
        let attrs = self
            .env_query
            .get_local_attributes(impl_item.owner_id.def_id);
        if has_spec_only_attr(attrs) || has_extern_spec_attr(attrs) {
            return;
        }

        // Skip associated types and other non-methods items
        if let hir::ImplItemKind::Fn(..) = impl_item.kind {
            // continue
        } else {
            return;
        }

        let def_id = self
            .env_query
            .as_local_def_id(impl_item.hir_id())
            .to_def_id();
        let item_def_path = self.env_name.get_item_def_path(def_id);
        trace!("Add {} to procedures", item_def_path);
        self.procedures.push(def_id);
    }

    fn visit_foreign_item(&mut self, _foreign_item: &hir::ForeignItem) {
        // Nothing
    }
}
