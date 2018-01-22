// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

use data::ProcedureDefId;

#[derive(Debug, Default, PartialEq, Eq, Hash, Clone, Copy)]
/// Epoch uniquely identifies the state of the environment. In other
/// words, if the epoch is the same, then we are verifying still exactly
/// the same program.
///
/// The main idea of epochs is to allow reducing the amount of code that
/// is sent to the back-end verifier because presence of many irrelevant
/// terms can significantly slow down the prover.
/// A unique identifier of the Rust procedure.
pub struct Epoch(usize);

impl Epoch {
    /// Constructor.
    pub fn new() -> Self {
        Self { 0: 1 }
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
/// A unique identifier of the Prusti Basic Block.
pub struct BasicBlockDefId(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
/// A unique identifier of the loop.
pub struct LoopDefId(usize);

#[derive(Debug)]
/// The type of the basic block.
pub enum BasicBlockType {
    /// The initial basic block.
    Start,
    /// The final basic block.
    End,
    /// A simple basic block.
    Simple,
    /// A loop head that also includes the computation of the loop
    /// condition.
    LoopHead(LoopDefId),
}

/// An incoming edge into a basic block.
pub enum BasicBlockInEdge {
    /// A simple transition between basic blocks.
    Simple,
    /// An edge that goes from the loop head.
    LoopEnter(LoopDefId),
    /// An edge that leaves the loop (the start basic block is dominated
    /// by the loop head and the target basic block is not dominated).
    LoopExit(LoopDefId),
}

/// An outgoing edge from a basic block.
pub enum BasicBlockOutEdge {
    /// A simple transition between basic blocks.
    Simple(BasicBlockDefId),
    /// The current basic block is a loop head and the target of this
    /// edge is a basic block dominated by the current basic block.
    LoopEnter(BasicBlockDefId),
    /// An edge that leaves the loop (the start basic block is dominated
    /// by the loop head and the target basic block is not dominated).
    ///
    /// Note that if the current basic block is a loop head, then all
    /// edges are either `LoopEnter` or `LoopExit`.
    LoopExit(BasicBlockDefId, LoopDefId),
}

/// A basic block of the Prusti CFG.
pub trait BasicBlock {
    /// Get definition ID of the basic block.
    fn get_id(&self) -> BasicBlockDefId;

    /// Get the type of the basic block.
    fn get_type(&self) -> BasicBlockType;

    /// Get edges that go into this basic block.
    fn get_in_edges(&self) -> Vec<BasicBlockInEdge>;

    /// Get edges that go out of this basic block.
    fn get_out_edges(&self) -> Vec<BasicBlockOutEdge>;
}

/// A CFG visitor that visits each basic block exactly once.
///
/// CFG format used by Prusti is described (TODO: make a precise link)
/// [here](https://viperproject.github.io/prusti-dev/design/03_workflow.html).
pub trait OnceCFGVisitor {
    /// Visit a basic block.
    fn visit_block(&mut self, block: &BasicBlock);
}

/// A facade that provides information about the Rust procedure.
pub trait Procedure {
    /// Get definition ID of the procedure.
    fn get_id(&self) -> ProcedureDefId;

    /// A visitor that traverses each basic block exactly once.
    fn walk_once(&self, visitor: &mut OnceCFGVisitor);
}

/// A facade to the Rust compiler.
pub trait Environment {
    /// Get the current epoch.
    fn get_current_epoch(&self) -> Epoch;

    /// Get a Procedure.
    fn get_procedure(&self, procedure_id: ProcedureDefId) -> Box<Procedure>;
}
