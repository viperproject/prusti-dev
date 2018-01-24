// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::Epoch;
use prusti_interface::environment::Environment as EnvironmentSpec;
use prusti_interface::environment::Procedure;
use prusti_interface::data::ProcedureDefId;
use rustc_driver::driver;

/// Facade to the Rust compiler.
pub struct Environment<'r, 'a: 'r, 'tcx: 'a> {
    state: &'r mut driver::CompileState<'a, 'tcx>
}

impl<'r, 'a, 'tcx> Environment<'r, 'a, 'tcx> {
    pub fn new(state: &'r mut driver::CompileState<'a, 'tcx>) -> Self {
        Environment { state }
    }
}

impl<'r, 'a, 'tcx> EnvironmentSpec for Environment<'r, 'a, 'tcx> {
    /// Get the current epoch.
    fn get_current_epoch(&self) -> Epoch {
        Epoch::new()
    }

    fn get_procedure(&self, _: ProcedureDefId) -> Box<Procedure> {
        unimplemented!()
    }
}
