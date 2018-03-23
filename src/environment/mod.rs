// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

mod procedure;

use data::ProcedureDefId;
pub use self::procedure::{BasicBlockIndex, Procedure, ProcedureImpl};

/// A facade to the Rust compiler.
pub trait Environment<'tcx> {
    type ProcedureImpl: Procedure<'tcx>;

    fn get_procedure_name(&self, proc_def_id: ProcedureDefId) -> String;

    /// Get a Procedure.
    fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Self::ProcedureImpl;
}
