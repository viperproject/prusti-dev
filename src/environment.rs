// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

use data::ProcedureDefId;
use rustc::mir;

pub type BasicBlockIndex = mir::BasicBlock;
pub type BasicBlockData<'tcx> = mir::BasicBlockData<'tcx>;

/// A facade that provides information about the Rust procedure.
pub trait Procedure {
    /// Get definition ID of the procedure.
    fn get_id(&self) -> ProcedureDefId;

    /// Iterate over all CFG basic blocks
    fn walk_once_raw_cfg<F>(&self, mut visitor: F) where F: FnMut(BasicBlockIndex, &BasicBlockData);

    /// Iterate over all CFG basic blocks that are not part of the specification type checking
    fn walk_once_cfg<F>(&self, mut visitor: F) where F: FnMut(BasicBlockIndex, &BasicBlockData);
}

/// A facade to the Rust compiler.
pub trait Environment {
    type ProcedureImpl: Procedure;

    /// Get a Procedure.
    fn get_procedure(&self, proc_def_id: ProcedureDefId) -> Self::ProcedureImpl;
}
