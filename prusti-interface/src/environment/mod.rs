// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

use prusti_rustc_interface::middle::ty::{self, TyCtxt};

pub mod body;
pub mod borrowck;
mod collect_closure_defs_visitor;
mod collect_prusti_spec_visitor;
pub mod debug_utils;
mod diagnostic;
mod dump_borrowck_info;
mod loops;
mod loops_utils;
pub mod mir_analyses;
pub mod mir_body;
pub mod mir_dump;
pub mod mir_sets;
pub mod mir_storage;
pub mod mir_utils;
mod name;
pub mod polonius_info;
mod procedure;
mod query;

pub use self::{
    body::EnvBody,
    diagnostic::EnvDiagnostic,
    loops::{LoopAnalysisError, PlaceAccess, PlaceAccessKind, ProcedureLoops},
    loops_utils::*,
    name::EnvName,
    procedure::{
        get_loop_invariant, is_checked_block_begin_marker, is_checked_block_end_marker,
        is_ghost_begin_marker, is_ghost_end_marker, is_loop_invariant_block, is_loop_variant_block,
        is_marked_specification_block, is_specification_begin_marker, is_specification_end_marker,
        is_try_finally_begin_marker, is_try_finally_end_marker, BasicBlockIndex, Procedure,
    },
    query::EnvQuery,
};
use self::{
    collect_closure_defs_visitor::CollectClosureDefsVisitor,
    collect_prusti_spec_visitor::CollectPrustiSpecVisitor,
};
use crate::data::ProcedureDefId;
use rustc_middle::ty::SubstsRef;

/// Facade to the Rust compiler.
pub struct Environment<'tcx> {
    prusti_version: &'static str,
    pub body: EnvBody<'tcx>,
    pub diagnostic: EnvDiagnostic<'tcx>,
    pub name: EnvName<'tcx>,
    pub query: EnvQuery<'tcx>,
}

impl<'tcx> Environment<'tcx> {
    /// Builds an environment given a compiler state.
    pub fn new(tcx: TyCtxt<'tcx>, prusti_version: &'static str) -> Self {
        Environment {
            prusti_version,
            body: EnvBody::new(tcx),
            diagnostic: EnvDiagnostic::new(tcx),
            name: EnvName::new(tcx),
            query: EnvQuery::new(tcx),
        }
    }

    /// Returns the typing context
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.query.tcx()
    }

    /// Dump various information from the borrow checker.
    ///
    /// Mostly used for experiments and debugging.
    pub fn dump_borrowck_info(&self, procedures: &[ProcedureDefId]) {
        if prusti_common::config::dump_borrowck_info() {
            dump_borrowck_info::dump_borrowck_info(self, procedures)
        }
    }

    /// Get a Procedure.
    pub fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Procedure<'tcx> {
        Procedure::new(self, proc_def_id)
    }

    /// Get ids of Rust procedures that are annotated with a Prusti specification
    #[tracing::instrument(level = "debug", skip(self))]
    pub fn get_annotated_procedures_and_types(&self) -> (Vec<ProcedureDefId>, Vec<ty::Ty<'tcx>>) {
        let mut visitor = CollectPrustiSpecVisitor::new(self);
        visitor.visit_all_item_likes();

        let mut cl_visitor = CollectClosureDefsVisitor::new(self);
        self.query
            .hir()
            .visit_all_item_likes_in_crate(&mut cl_visitor);

        let (mut procedures, types) = visitor.into_result();
        procedures.extend(cl_visitor.get_closure_defs());
        (procedures, types)
    }

    /// Compare the current version of the `prusti` crate to the given other version
    pub fn compare_prusti_version(&self, other: &str) -> std::cmp::Ordering {
        version_compare::compare(self.prusti_version, other)
            .unwrap_or_else(|_| {
                panic!(
                    "Failed to compare Prusti version '{}' with other version '{other}'!",
                    self.prusti_version
                )
            })
            .ord()
            .unwrap()
    }

    /// Get the current version of the `prusti` crate
    pub fn get_prusti_version(&self) -> &'static str {
        self.prusti_version
    }

    /// Compare to the current version of the `prusti-specs` crate which we've been compiled with
    pub fn compare_to_curr_specs_version(other: &str) -> std::cmp::Ordering {
        let compiled_specs_version = prusti_specs::SPECS_VERSION;
        version_compare::compare(compiled_specs_version, other)
            .unwrap_or_else(|_| {
                panic!(
                    "Failed to compare `prusti-specs` version '{}' with found version '{other}'!",
                    prusti_specs::SPECS_VERSION
                )
            })
            .ord()
            .unwrap()
    }

    pub fn callee_reaches_caller(
        &self,
        caller_def_id: ProcedureDefId,
        called_def_id: ProcedureDefId,
        call_substs: SubstsRef<'tcx>,
    ) -> bool {
        if called_def_id != caller_def_id && called_def_id.is_local() {
            let param_env = self.tcx().param_env(caller_def_id);
            if let Some(instance) = self
                .tcx()
                .resolve_instance(param_env.and((called_def_id, call_substs)))
                .unwrap()
            {
                return self
                    .tcx()
                    .mir_callgraph_reachable((instance, caller_def_id.expect_local()));
            }
        }
        called_def_id.is_local() // FIXME: Currently assuming that external ids are not recursive.
    }

    /// Get the current version of the `prusti` crate
    pub fn get_specs_version() -> &'static str {
        prusti_specs::SPECS_VERSION
    }
}
