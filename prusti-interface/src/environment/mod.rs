// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

use rustc_driver::driver;
use rustc::ty::TyCtxt;
use rustc::hir::def_id::DefId;
use std::path::PathBuf;
use syntax_pos::FileName;
use syntax_pos::MultiSpan;
use syntax::errors::DiagnosticId;
use rustc::hir;
use rustc::ty;
use syntax::attr;

mod procedure;
mod loops;
mod loops_utils;
mod collect_prusti_spec_visitor;
mod dump_borrowck_info;
pub mod borrowck;
pub mod mir_analyses;
pub mod place_set;
pub mod polonius_info;

use data::ProcedureDefId;
pub use self::procedure::{BasicBlockIndex, Procedure};
pub use self::loops::{ProcedureLoops, PlaceAccess, PlaceAccessKind};
pub use self::loops_utils::*;
use self::collect_prusti_spec_visitor::CollectPrustiSpecVisitor;
use syntax::codemap::CodeMap;
use utils::get_attr_value;
use config;
use syntax::codemap::Span;

/// Facade to the Rust compiler.
pub struct EnvironmentImpl<'r, 'a: 'r, 'tcx: 'a> {
    state: &'r mut driver::CompileState<'a, 'tcx>,
}

impl<'r, 'a, 'tcx> EnvironmentImpl<'r, 'a, 'tcx> {
    /// Builds an environment given a compiler state.
    pub fn new(state: &'r mut driver::CompileState<'a, 'tcx>) -> Self {
        EnvironmentImpl { state }
    }

    /// Returns the path of the source that is being compiled
    pub fn source_path(&self) -> PathBuf {
        match driver::source_name(self.state.input) {
            FileName::Real(path) => path,
            _ => unreachable!(),
        }
    }

    /// Returns the name of the crate that is being compiled
    pub fn crate_name(&self) -> &str {
        self.state.crate_name.as_ref().unwrap()
    }

    /// Returns the typing context
    pub fn tcx(&self) -> TyCtxt<'a, 'tcx, 'tcx> {
        self.state.tcx.unwrap()
    }

    /// Returns the type of a `HirId`
    pub fn hir_id_to_type(&self, hir_id: hir::HirId) -> ty::Ty<'tcx> {
        let owner_def_id = hir_id.owner_def_id();
        let typeck_tables = self.tcx().typeck_tables_of(owner_def_id);
        typeck_tables.node_id_to_type(hir_id)
    }

    /// Returns the `CodeMap`
    pub fn codemap(&self) -> &'tcx CodeMap {
        self.state.session.codemap()
    }

    /// Emits a warning message
    pub fn warn(&self, msg: &str) {
        self.state.session.warn(msg);
    }

    /// Emits an warning message.
    pub fn span_warn<S: Into<MultiSpan>>(&self, sp: S, msg: &str) {
        self.state.session.span_warn(sp, msg);
    }

    /// Emits an error message.
    pub fn err(&self, msg: &str) {
        self.state.session.err(msg);
    }

    /// Emits an error message.
    pub fn span_err<S: Into<MultiSpan>>(&self, sp: S, msg: &str) {
        self.state.session.span_err(sp, msg);
    }

    /// Emits an error message.
    pub fn span_err_with_code<S: Into<MultiSpan>>(&self, sp: S, msg: &str, code: String) {
        self.state.session.span_err_with_code(sp, msg, DiagnosticId::Error(code));
    }

    /// Emits an error message.
    pub fn err_with_code(&self, msg: &str, code: String) {
        self.span_err_with_code(MultiSpan::new(), msg, code);
    }

    /// Emits an error message.
    pub fn span_err_with_code_with_reason<S: Into<MultiSpan>>(
        &self,
        sp: S,
        msg: &str,
        code: String,
        reason_sp: S,
    ) {
        let mut diagnostic = self.state.session.struct_err_with_code(
            msg, DiagnosticId::Error(code));
        diagnostic.set_span(sp);
        diagnostic.span_note(reason_sp, "the failing assertion is this one");
        diagnostic.emit();
    }

    /// Returns true if an error has been emitted
    pub fn has_errors(&self) -> bool {
        self.state.session.has_errors()
    }

    /// Aborts in case of error.
    pub fn abort_if_errors(&self) {
        self.state.session.abort_if_errors();
    }

    /// Get ids of Rust procedures that are annotated with a Prusti specification
    pub fn get_annotated_procedures(&self) -> Vec<ProcedureDefId> {
        let mut annotated_procedures: Vec<ProcedureDefId> = vec![];
        let tcx = self.tcx();
        {
            let mut visitor = CollectPrustiSpecVisitor::new(self, &mut annotated_procedures);
            tcx.hir.krate().visit_all_item_likes(&mut visitor);
        }
        annotated_procedures
    }

    pub fn get_attr(&self, def_id: ProcedureDefId, name: &str) -> Option<String> {
        let tcx = self.tcx();
        let opt_node_id = tcx.hir.as_local_node_id(def_id);
        match opt_node_id {
            None => None,
            Some(node_id) => {
                tcx.hir.attrs(node_id).iter()
                    .find(|item| item.path.to_string() == name)
                    .map(get_attr_value)
            }
        }
    }

    /// Find whether the procedure has a particular attribute
    pub fn has_attribute_name(&self, def_id: ProcedureDefId, name: &str) -> bool {
        let tcx = self.tcx();
        let opt_node_id = tcx.hir.as_local_node_id(def_id);
        match opt_node_id {
            None => {
                debug!("Incomplete encoding of procedures from an external crate");
                false
            }
            Some(node_id) => {
                attr::contains_name(tcx.hir.attrs(node_id), name)
            }
        }
    }

    /// Dump various information from the borrow checker.
    ///
    /// Mostly used for experiments and debugging.
    pub fn dump_borrowck_info(&self, procedures: &Vec<ProcedureDefId>) {
        if config::dump_borrowck_info() {
            dump_borrowck_info::dump_borrowck_info(self.tcx(), procedures)
        }
    }

    /// Get an absolute `def_path`. Note: not preserved across compilations!
    pub fn get_item_def_path(&self, def_id: DefId) -> String {
        let def_path = self.tcx().def_path(def_id);
        let mut crate_name = self.tcx().crate_name(def_path.krate).to_string();
        crate_name.push_str(&def_path.to_string_no_crate());
        crate_name
    }

    /// Get the span of a definition
    /// Note: panics on non-local `def_id`
    pub fn get_item_span(&self, def_id: DefId) -> Span {
        self.tcx().hir.span_if_local(def_id).unwrap()
    }

    pub fn get_item_name(&self, def_id: DefId) -> String {
        self.tcx().absolute_item_path_str(def_id)
    }

    /// Get a Procedure.
    pub fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Procedure<'a, 'tcx> {
        Procedure::new(self.tcx(), proc_def_id)
    }
}
