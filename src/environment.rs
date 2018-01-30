// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A module that defines the compiler's facade used by the verifier.

use prusti_interface::environment::Epoch;
use prusti_interface::environment::Environment as EnvironmentSpec;
use prusti_interface::environment::Procedure;
use prusti_interface::data::ProcedureDefId;
use rustc_driver::driver;

/// Facade to the Rust compiler.
pub struct Environment<'r, 'a: 'r, 'tcx: 'a> {
    state: &'r mut driver::CompileState<'a, 'tcx>,
}

impl<'r, 'a, 'tcx> Environment<'r, 'a, 'tcx> {
    /// Builds an environment given a compiler state.
    pub fn new(state: &'r mut driver::CompileState<'a, 'tcx>) -> Self {
        Environment { state }
    }

    /// Dumps useful information
    pub fn dump(&self) {
        trace!("[dump] enter");

        //debug!("{:?}", self.state.tcx);

        //self.state.tcx.unwrap().

        trace!("[dump] exit");
    }

    /// Emits a warning message
    pub fn warn(&self, msg: &str) {
        self.state.session.warn(msg);
    }

    /// Emits an error message.
    pub fn err(&self, msg: &str) {
        self.state.session.err(msg);
    }

    /// Aborts the compilation and exits with an error code if some error has been emitted so far.
    ///
    /// TODO: check if compiler plugins have to call this method on their own.
    pub fn abort_if_errors(&self) {
        self.state.session.abort_if_errors();
    }
}

impl<'r, 'a, 'tcx> EnvironmentSpec for Environment<'r, 'a, 'tcx> {
    fn get_current_epoch(&self) -> Epoch {
        Epoch::new()
    }

    fn get_procedure(&self, _: ProcedureDefId) -> Box<Procedure> {
        unimplemented!()
    }
}
