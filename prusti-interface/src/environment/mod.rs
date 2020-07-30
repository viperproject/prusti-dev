// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

use rustc_hir::hir_id::HirId;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use std::path::PathBuf;

use rustc_span::{Span, MultiSpan, symbol::Symbol};
use rustc_hir as hir;
// use rustc::hir::def_id::DefId;
// use rustc::ty;
// use rustc::ty::TyCtxt;
// use rustc_driver::driver;
use std::collections::HashSet;
// use syntax::attr;
// use syntax_pos::FileName;
// use syntax_pos::MultiSpan;
// use syntax_pos::symbol::Symbol;

pub mod borrowck;
mod collect_prusti_spec_visitor;
mod dump_borrowck_info;
mod loops;
mod loops_utils;
pub mod mir_analyses;
pub mod place_set;
pub mod polonius_info;
mod procedure;

use self::collect_prusti_spec_visitor::CollectPrustiSpecVisitor;
pub use self::loops::{PlaceAccess, PlaceAccessKind, ProcedureLoops};
pub use self::loops_utils::*;
pub use self::procedure::{BasicBlockIndex, Procedure};
// use config;
use crate::data::ProcedureDefId;
// use syntax::codemap::CodeMap;
// use syntax::codemap::Span;
// use utils::get_attr_value;
use rustc_span::source_map::SourceMap;

/// Facade to the Rust compiler.
// #[derive(Copy, Clone)]
pub struct Environment<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Environment<'tcx> {
    /// Builds an environment given a compiler state.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Environment { tcx }
    }

    /// Returns the path of the source that is being compiled
    pub fn source_path(&self) -> PathBuf {
        self.tcx.sess.local_crate_source_file.clone().unwrap()
    }

    /// Returns the name of the crate that is being compiled
    pub fn crate_name(&self) -> String {
        self.tcx
            .crate_name(rustc_span::def_id::LOCAL_CRATE)
            .to_string()
    }

    /// Returns the typing context
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Returns the type of a `HirId`
    pub fn hir_id_to_type(&self, hir_id: HirId) -> ty::Ty<'tcx> {
        let def_id = self.tcx.hir().local_def_id(hir_id);
        self.tcx.type_of(def_id)
    }

    /// Returns the `CodeMap`
    pub fn codemap(&self) -> &'tcx SourceMap {
        self.tcx.sess.source_map()
    }

    // /// Emits a warning message
    // pub fn warn(&self, msg: &str) {
    //     self.state.session.warn(msg);
    // }

    // /// Emits an warning message.
    // pub fn span_warn<S: Into<MultiSpan>>(&self, sp: S, msg: &str) {
    //     self.state.session.span_warn(sp, msg);
    // }

    // /// Emits an error message.
    // pub fn err(&self, msg: &str) {
    //     self.state.session.err(msg);
    // }

    // /// Emits an error message.
    // pub fn span_err<S: Into<MultiSpan>>(&self, sp: S, msg: &str) {
    //     self.state.session.span_err(sp, msg);
    // }

    /// Emits an error message.
    pub fn span_err_with_help_and_note<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        note: &Option<(String, S)>
    ) {
        let mut diagnostic = self.tcx.sess.struct_err(msg);
        diagnostic.set_span(sp);
        if let Some(help_msg) = help {
            diagnostic.help(help_msg);
        }
        if let Some((note_msg, note_sp)) = note {
            diagnostic.span_note(note_sp.clone(), note_msg);
        }
        diagnostic.emit();
    }

    /// Emits an error message.
    pub fn span_warn_with_help_and_note<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        note: &Option<(String, S)>
    ) {
        let mut diagnostic = self.tcx.sess.struct_warn(msg);
        diagnostic.set_span(sp);
        if let Some(help_msg) = help {
            diagnostic.help(help_msg);
        }
        if let Some((note_msg, note_sp)) = note {
            diagnostic.span_note(note_sp.clone(), note_msg);
        }
        diagnostic.emit();
    }

    /// Returns true if an error has been emitted
    pub fn has_errors(&self) -> bool {
        self.tcx.sess.has_errors()
    }

    // /// Aborts in case of error.
    // pub fn abort_if_errors(&self) {
    //     self.state.session.abort_if_errors();
    // }

    /// Get ids of Rust procedures that are annotated with a Prusti specification
    pub fn get_annotated_procedures(&self) -> Vec<ProcedureDefId> {
        let tcx = self.tcx;
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        tcx.hir().krate().visit_all_item_likes(&mut visitor);
        visitor.get_annotated_procedures()
    }

    // TODO: Use encoder.get_opt_spec_id instead.
    // pub fn get_attr(&self, def_id: ProcedureDefId, name: &str) -> Option<String> {
    //     let tcx = self.tcx();
    //     let opt_node_id = tcx.hir.as_local_node_id(def_id);
    //     match opt_node_id {
    //         None => None,
    //         Some(node_id) => tcx
    //             .hir
    //             .attrs(node_id)
    //             .iter()
    //             .find(|item| item.path.to_string() == name)
    //             .map(get_attr_value),
    //     }
    // }

    /// Find whether the procedure has a particular attribute
    pub fn has_attribute_name(&self, def_id: ProcedureDefId, name: &str) -> bool {
        let tcx = self.tcx();
        crate::environment::collect_prusti_spec_visitor::contains_name(tcx.get_attrs(def_id), name)
    }

    /// Dump various information from the borrow checker.
    ///
    /// Mostly used for experiments and debugging.
    pub fn dump_borrowck_info(&self, procedures: &Vec<ProcedureDefId>) {
        if prusti_common::config::dump_borrowck_info() {
            dump_borrowck_info::dump_borrowck_info(self.tcx(), procedures)
        }
    }

    /// Get an absolute `def_path`. Note: not preserved across compilations!
    pub fn get_item_def_path(&self, def_id: DefId) -> String {
        let def_path = self.tcx.def_path(def_id);
        let mut crate_name = self.tcx.crate_name(def_path.krate).to_string();
        crate_name.push_str(&def_path.to_string_no_crate());
        crate_name
    }

    /// Get the span of a definition
    /// Note: panics on non-local `def_id`
    pub fn get_item_span(&self, def_id: DefId) -> Span {
        self.tcx.hir().span_if_local(def_id).unwrap()
    }

    pub fn get_absolute_item_name(&self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
    }

    pub fn get_item_name(&self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
        // self.tcx().item_path_str(def_id)
    }

    /// Get a Procedure.
    pub fn get_procedure<'a>(&'a self, proc_def_id: ProcedureDefId) -> Procedure<'a, 'tcx> {
        Procedure::new(self.tcx(), proc_def_id)
    }

    /// Get all relevant trait declarations for some type.
    pub fn get_traits_decls_for_type(&self, ty: &ty::Ty<'tcx>) -> HashSet<DefId> {
        let mut res = HashSet::new();
        let krate = hir::def_id::LOCAL_CRATE;
        let traits = self.tcx().all_traits(krate);
        for trait_id in traits.iter() {
            self.tcx().for_each_relevant_impl(*trait_id, ty, |impl_id| {
                if let Some(relevant_trait_id) = self.tcx().trait_id_of_impl(impl_id) {
                    res.insert(relevant_trait_id.clone());
                }
            });
        }
        res
    }

    /// Get an associated item by name.
    pub fn get_assoc_item(&self, id: DefId, name: Symbol) -> Option<ty::AssocItem> {
        // FIXME: Probably we should use https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.AssociatedItems.html#method.find_by_name_and_namespace
        // instead.
        self.tcx().associated_items(id).filter_by_name_unhygienic(name).next().cloned()
    }

    // /// Get a trait method declaration by name for type.
    // pub fn get_trait_method_decl_for_type(&self, typ: ty::Ty<'tcx>, trait_id: DefId, name: Symbol) -> Vec<ty::AssociatedItem> {
    //     let mut result = Vec::new();
    //     self.tcx().for_each_relevant_impl(trait_id, typ, |impl_id| {
    //         let item = self.get_assoc_item(impl_id, name);
    //         if let Some(inner) = item {
    //             result.push(inner.clone());
    //         }
    //     });
    //     result
    // }
}
