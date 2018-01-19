// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.

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

/// A facade to the Rust compiler.
pub trait Environment {
    /// Get the current epoch.
    fn get_current_epoch(&self) -> Epoch;
}
