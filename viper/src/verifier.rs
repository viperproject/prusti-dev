// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::VerificationResult;
use crate::jar::viper::silver;
use duchess::GlobalResult;

pub enum VerificationBackend {
    Carbon,
    Silicon,
}

pub struct Verifier {
    verifier_obj: silver::verifier::Verifier,
}

impl Verifier {
    /// Creates a new verifier, internally constructing the Java object of the verifier.
    pub fn new(backend: VerificationBackend) -> GlobalResult<Self> {
        todo!()
    }

    /// Creates a new verifier with arguments, internally constructing the Java object of the
    /// verifier.
    pub fn new_with_args(backend: VerificationBackend, args: Vec<String>) -> GlobalResult<Self> {
        todo!()
    }

    /// Builds the Java object of the program, verifies it, and returns a verification result.
    pub fn verify(&self, program: &silver::ast::Program) -> GlobalResult<VerificationResult> {
        todo!()
    }
}
