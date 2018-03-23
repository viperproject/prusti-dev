// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that defines the compiler's facade used by the verifier.

use prusti_interface::environment::Environment as EnvironmentSpec;
use prusti_interface::data::ProcedureDefId;
use rustc_driver::driver;
use rustc::ty::TyCtxt;

mod collect_prusti_spec_visitor;
mod dump_borrowck_info;
mod procedure;
use self::collect_prusti_spec_visitor::CollectPrustiSpecVisitor;
use self::dump_borrowck_info::dump_borrowck_info;
pub use self::procedure::Procedure;

/// Facade to the Rust compiler.
pub struct Environment<'r, 'a: 'r, 'tcx: 'a> {
    state: &'r mut driver::CompileState<'a, 'tcx>,
}

impl<'r, 'a, 'tcx> Environment<'r, 'a, 'tcx> {
    /// Builds an environment given a compiler state.
    pub fn new(state: &'r mut driver::CompileState<'a, 'tcx>) -> Self {
        Environment { state }
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

    /// Dump various information from the borrow checker.
    ///
    /// Mostly used for experiments and debugging.
    pub fn dump_borrowck_info(&self) {
        dump_borrowck_info(self.tcx())
    }
}

impl<'r, 'a, 'tcx> EnvironmentSpec<'tcx> for Environment<'r, 'a, 'tcx> {
    type ProcedureImpl = Procedure<'a, 'tcx>;

    fn get_procedure_name(&self, proc_def_id: ProcedureDefId) -> String {
        self.tcx().item_path_str(proc_def_id)
    }

    /// Get a Procedure.
    fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Procedure<'a, 'tcx> {
        Procedure::new(self.tcx(), proc_def_id)
    }
}
