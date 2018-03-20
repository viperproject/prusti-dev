// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

use data::ProcedureDefId;
use rustc::mir;

pub type BasicBlockIndex = mir::BasicBlock;
pub type BasicBlockData = mir::BasicBlockData;

/// A CFG visitor that visits each basic block exactly once.
///
/// CFG format used by Prusti is described (TODO: make a precise link)
/// [here](https://viperproject.github.io/prusti-dev/design/03_workflow.html).
pub trait OnceCFGVisitor {
    /// Visit a basic block.
    fn visit_block(&mut self, index: BasicBlockIndex, block: &BasicBlockData);
}

/// A facade that provides information about the Rust procedure.
pub trait Procedure {
    /// Get definition ID of the procedure.
    fn get_id(&self) -> ProcedureDefId;
}

/// A facade to the Rust compiler.
pub trait Environment {
    /// Get a Procedure.
    fn get_procedure(&self, procedure_id: ProcedureDefId) -> Box<Procedure>;
}
