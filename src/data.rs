// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines data structures exchanged between a verifier and
//! its environment.

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
/// A unique identifier of the Rust procedure.
pub struct ProcedureDefId(usize);

/// A generator that generates unique procedure def ids.
#[derive(Debug)]
pub struct ProcedureDefIdGenerator {
    last_value: ProcedureDefId,
}

impl ProcedureDefIdGenerator {
    /// Constructor.
    pub fn new() -> Self {
        Self {
            last_value: ProcedureDefId(1),
        }
    }
    /// Generate a new unique ID.
    pub fn get_new_id(&mut self) -> ProcedureDefId {
        self.last_value = ProcedureDefId(self.last_value.0 + 1);
        self.last_value
    }
}

impl Default for ProcedureDefIdGenerator {
    fn default() -> Self {
        Self::new()
    }
}

/// A list of items to verify that is passed to a verifier.
pub struct VerificationTask {
    /// A list of procedures to verify.
    pub procedures: Vec<ProcedureDefId>,
}

/// Verification result returned by a verifier.
pub enum VerificationResult {
    /// Verification was successful.
    Success,
    /// Verification failed. Errors should have been already emitted by
    /// the verifier.
    Failure,
}

#[derive(Debug, PartialEq, Eq, Hash)]
/// A Rust procedure
pub struct Procedure {
    // TODO mir: Mir?
}
