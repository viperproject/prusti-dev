// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

use rustc_ast::ast;
use rustc_hir as hir;
use rustc_middle::mir;
use rustc_hir::hir_id::HirId;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{self, TyCtxt, ParamEnv, WithOptConstParam};
use rustc_trait_selection::infer::{TyCtxtInferExt, InferCtxtExt};
use std::path::PathBuf;
use std::cell::Ref;
use rustc_span::{Span, MultiSpan, symbol::Symbol};
use std::collections::HashSet;
use log::debug;
use std::rc::Rc;
use std::collections::HashMap;
use std::cell::RefCell;

pub mod borrowck;
mod collect_prusti_spec_visitor;
mod collect_closure_defs_visitor;
mod dump_borrowck_info;
mod loops;
mod loops_utils;
pub mod mir_analyses;
pub mod mir_storage;
pub mod mir_utils;
pub mod place_set;
pub mod polonius_info;
mod procedure;

use self::collect_prusti_spec_visitor::CollectPrustiSpecVisitor;
use self::collect_closure_defs_visitor::CollectClosureDefsVisitor;
use rustc_hir::intravisit::Visitor;
pub use self::loops::{PlaceAccess, PlaceAccessKind, ProcedureLoops};
pub use self::loops_utils::*;
pub use self::procedure::{BasicBlockIndex, Procedure};
use self::borrowck::facts::BorrowckFacts;
// use config;
use crate::data::ProcedureDefId;
// use syntax::codemap::CodeMap;
// use syntax::codemap::Span;
// use utils::get_attr_value;
use rustc_span::source_map::SourceMap;

/// Facade to the Rust compiler.
// #[derive(Copy, Clone)]
pub struct Environment<'tcx> {
    /// Cached MIR bodies.
    bodies: RefCell<HashMap<LocalDefId, Rc<mir::Body<'tcx>>>>,
    /// Cached borrowck information.
    borrowck_facts: RefCell<HashMap<LocalDefId, Rc<BorrowckFacts>>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Environment<'tcx> {
    /// Builds an environment given a compiler state.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Environment {
            tcx,
            bodies: RefCell::new(HashMap::new()),
            borrowck_facts: RefCell::new(HashMap::new()),
        }
    }

    /// Returns the path of the source that is being compiled
    pub fn source_path(&self) -> PathBuf {
        self.tcx.sess.local_crate_source_file.clone().unwrap()
    }

    /// Returns the file name of the source that is being compiled
    pub fn source_file_name(&self) -> String {
        let source_path = self.source_path();
        source_path.file_name().unwrap().to_str().unwrap().to_owned()
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
    pub fn span_err_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.sess.struct_err(msg);
        diagnostic.set_span(sp);
        if let Some(help_msg) = help {
            diagnostic.help(help_msg);
        }
        for (note_msg, opt_note_sp) in notes {
            if let Some(note_sp) = opt_note_sp {
                diagnostic.span_note(note_sp.clone(), note_msg);
            } else {
                diagnostic.note(note_msg);
            }
        }
        diagnostic.emit();
    }

    /// Emits an error message.
    pub fn span_warn_with_help_and_notes<S: Into<MultiSpan> + Clone>(
        &self,
        sp: S,
        msg: &str,
        help: &Option<String>,
        notes: &[(String, Option<S>)],
    ) {
        let mut diagnostic = self.tcx.sess.struct_warn(msg);
        diagnostic.set_span(sp);
        if let Some(help_msg) = help {
            diagnostic.help(help_msg);
        }
        for (note_msg, opt_note_sp) in notes {
            if let Some(note_sp) = opt_note_sp {
                diagnostic.span_note(note_sp.clone(), note_msg);
            } else {
                diagnostic.note(note_msg);
            }
        }
        diagnostic.emit();
    }

    /// Returns true if an error has been emitted
    pub fn has_errors(&self) -> bool {
        self.tcx.sess.has_errors()
    }

    /// Get ids of Rust procedures that are annotated with a Prusti specification
    pub fn get_annotated_procedures(&self) -> Vec<ProcedureDefId> {
        let tcx = self.tcx;
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        tcx.hir().visit_all_item_likes(&mut visitor);

        let mut cl_visitor = CollectClosureDefsVisitor::new(self);
        tcx.hir().visit_all_item_likes(&mut cl_visitor.as_deep_visitor());

        let mut result: Vec<_> = visitor.get_annotated_procedures();
        result.extend(cl_visitor.get_closure_defs());
        result
    }

    /// Find whether the procedure has a particular `prusti::<name>` attribute.
    pub fn has_prusti_attribute(&self, def_id: ProcedureDefId, name: &str) -> bool {
        let tcx = self.tcx();
        crate::utils::has_prusti_attr(tcx.get_attrs(def_id), name)
    }

    /// Dump various information from the borrow checker.
    ///
    /// Mostly used for experiments and debugging.
    pub fn dump_borrowck_info(&self, procedures: &[ProcedureDefId]) {
        if prusti_common::config::dump_borrowck_info() {
            dump_borrowck_info::dump_borrowck_info(self, procedures)
        }
    }

    /// Get an absolute `def_path`. Note: not preserved across compilations!
    pub fn get_item_def_path(&self, def_id: DefId) -> String {
        let def_path = self.tcx.def_path(def_id);
        let mut crate_name = self.tcx.crate_name(def_path.krate).to_string();
        crate_name.push_str(&def_path.to_string_no_crate_verbose());
        crate_name
    }

    /// Get the span of the given definition.
    pub fn get_def_span(&self, def_id: DefId) -> Span {
        self.tcx.def_span(def_id)
    }

    pub fn get_absolute_item_name(&self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
    }

    pub fn get_item_name(&self, def_id: DefId) -> String {
        self.tcx.def_path_str(def_id)
        // self.tcx().item_path_str(def_id)
    }

    /// Get a Procedure.
    pub fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Procedure<'tcx> {
        Procedure::new(self, proc_def_id)
    }

    /// Get the MIR body of a local procedure.
    pub fn local_mir(&self, def_id: LocalDefId) -> Rc<mir::Body<'tcx>> {
        let mut bodies = self.bodies.borrow_mut();
        if let Some(body) = bodies.get(&def_id) {
            body.clone()
        } else {
            // SAFETY: This is safe because we are feeding in the same `tcx`
            // that was used to store the data.
            let body_with_facts = unsafe {
                self::mir_storage::retrieve_mir_body(self.tcx, def_id)
            };
            let body = body_with_facts.body;
            let facts = BorrowckFacts {
                input_facts: RefCell::new(Some(body_with_facts.input_facts)),
                output_facts: body_with_facts.output_facts,
                location_table: RefCell::new(Some(body_with_facts.location_table)),
            };

            let mut borrowck_facts = self.borrowck_facts.borrow_mut();
            borrowck_facts.insert(def_id, Rc::new(facts));

            bodies.entry(def_id).or_insert_with(|| {
                Rc::new(body)
            }).clone()
        }
    }

    /// Get Polonius facts of a local procedure.
    pub fn local_mir_borrowck_facts(&self, def_id: LocalDefId) -> Rc<BorrowckFacts> {
        let borrowck_facts = self.borrowck_facts.borrow();
        borrowck_facts.get(&def_id).unwrap().clone()
    }

    /// Get the MIR body of an external procedure.
    pub fn external_mir<'a>(&self, def_id: DefId) -> &'a mir::Body<'tcx> {
        self.tcx().optimized_mir(def_id)
    }

    /// Get all relevant trait declarations for some type.
    pub fn get_traits_decls_for_type(&self, ty: &ty::Ty<'tcx>) -> HashSet<DefId> {
        let mut res = HashSet::new();
        let traits = self.tcx().all_traits(());
        for trait_id in traits.iter() {
            self.tcx().for_each_relevant_impl(*trait_id, ty, |impl_id| {
                if let Some(relevant_trait_id) = self.tcx().trait_id_of_impl(impl_id) {
                    res.insert(relevant_trait_id);
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

    /// Get a trait method declaration by name for type.
    pub fn get_trait_method_decl_for_type(&self, typ: ty::Ty<'tcx>, trait_id: DefId, name: Symbol) -> Vec<ty::AssocItem> {
        let mut result = Vec::new();
        self.tcx().for_each_relevant_impl(trait_id, typ, |impl_id| {
            let item = self.get_assoc_item(impl_id, name);
            if let Some(inner) = item {
                result.push(inner);
            }
        });
        result
    }

    pub fn type_is_allowed_in_pure_functions(&self, ty: ty::Ty<'tcx>, param_env: ty::ParamEnv<'tcx>) -> bool {
        match ty.kind() {
            ty::TyKind::Never => {
                true
            }
            _ => {
                self.type_is_copy(ty, param_env)
            }
        }
    }

    pub fn type_is_copy(&self, ty: ty::Ty<'tcx>, param_env: ty::ParamEnv<'tcx>) -> bool {
        let copy_trait = self.tcx.lang_items().copy_trait();
        if let Some(copy_trait_def_id) = copy_trait {
            // We need this check because `type_implements_trait`
            // panics when called on reference types.
            if let ty::TyKind::Ref(_, _, mutability) = ty.kind() {
                // Shared references are copy, mutable references are not.
                matches!(mutability, mir::Mutability::Not)
            } else {
                self.type_implements_trait(ty, copy_trait_def_id, param_env)
            }
        } else {
            false
        }
    }

    /// Checks whether the given type implements the trait with the given DefId.
    pub fn type_implements_trait(&self, ty: ty::Ty<'tcx>, trait_def_id: DefId, param_env: ty::ParamEnv<'tcx>) -> bool {
        assert!(self.tcx.is_trait(trait_def_id));
        self.tcx.infer_ctxt().enter(|infcx|
            infcx
                .type_implements_trait(trait_def_id, ty, ty::List::empty(), param_env)
                .must_apply_considering_regions()
        )
    }
}
