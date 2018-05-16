// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

use rustc_driver::driver;
use rustc::ty::TyCtxt;
use rustc::hir::def_id::DefId;

mod procedure;
mod loops;
mod collect_prusti_spec_visitor;

use data::ProcedureDefId;
pub use self::procedure::{BasicBlockIndex, Procedure, ProcedureImpl};
pub use self::loops::{ProcedureLoops, PlaceAccess, PlaceAccessKind};
use self::collect_prusti_spec_visitor::CollectPrustiSpecVisitor;

/// A facade to the Rust compiler.
pub trait Environment<'tcx> {
    /// The concrete type that implements the Procedure interface
    type ProcedureImpl: Procedure<'tcx>;

    /// Get the name of an item
    fn get_item_name(&self, proc_def_id: DefId) -> String;

    /// Get a Procedure.
    fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Self::ProcedureImpl;
}

/// Facade to the Rust compiler.
pub struct EnvironmentImpl<'r, 'a: 'r, 'tcx: 'a> {
    state: &'r mut driver::CompileState<'a, 'tcx>,
}

impl<'r, 'a, 'tcx> EnvironmentImpl<'r, 'a, 'tcx> {
    /// Builds an environment given a compiler state.
    pub fn new(state: &'r mut driver::CompileState<'a, 'tcx>) -> Self {
        EnvironmentImpl { state }
    }

    /// Returns the typing context
    pub fn tcx(&self) -> TyCtxt<'a, 'tcx, 'tcx> {
        self.state.tcx.unwrap()
    }

    /// Emits a warning message
    pub fn warn(&self, msg: &str) {
        self.state.session.warn(msg);
    }

    /// Emits an error message.
    pub fn err(&self, msg: &str) {
        self.state.session.err(msg);
    }

    /// Get ids of Rust procedures that are annotated with a Prusti specification
    pub fn get_annotated_procedures(&self) -> Vec<ProcedureDefId> {
        let mut annotated_procedures: Vec<ProcedureDefId> = vec![];
        let tcx = self.tcx();
        {
            let mut visitor = CollectPrustiSpecVisitor::new(tcx, &mut annotated_procedures);
            tcx.hir.krate().visit_all_item_likes(&mut visitor);
        }
        annotated_procedures
    }
}

impl<'r, 'a, 'tcx> Environment<'tcx> for EnvironmentImpl<'r, 'a, 'tcx> {
    type ProcedureImpl = ProcedureImpl<'a, 'tcx>;

    fn get_item_name(&self, def_id: DefId) -> String {
        self.tcx().item_path_str(def_id)
    }

    /// Get a Procedure.
    fn get_procedure(&self, proc_def_id: ProcedureDefId) -> ProcedureImpl<'a, 'tcx> {
        ProcedureImpl::new(self.tcx(), proc_def_id)
    }
}
