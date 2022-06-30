// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{silicon_counterexample::SiliconCounterexample, JavaException};

/// The result of a verification request on a Viper program.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum VerificationResult {
    /// The program verified.
    Success,
    /// The program did not verify.
    Failure(Vec<VerificationError>),
    /// The program has consistency errors.
    ConsistencyErrors(Vec<String>),
    /// The verification raised a Java exception.
    JavaException(JavaException),
}

impl VerificationResult {
    pub fn is_success(&self) -> bool {
        matches!(self, Self::Success)
    }
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct VerificationError {
    pub full_id: String,
    // Unused since we get pos from the offending_node instead.
    // Currently calling pos on e.g. `ExhaleFailed` of Silver returns
    // the exhale expression pos, rather than the Exhale node pos.
    pub pos_id: Option<String>,
    pub offending_pos_id: Option<String>,
    pub reason_pos_id: Option<String>,
    pub message: String,
    pub counterexample: Option<SiliconCounterexample>,
}

impl VerificationError {
    pub fn new(
        full_id: String,
        pos_id: Option<String>,
        offending_pos_id: Option<String>,
        reason_pos_id: Option<String>,
        message: String,
        counterexample: Option<SiliconCounterexample>,
    ) -> Self {
        VerificationError {
            full_id,
            pos_id,
            offending_pos_id,
            reason_pos_id,
            message,
            counterexample,
        }
    }
}

/// The consistency error reported by the verifier.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ConsistencyError {
    /// To which method corresponds the program that triggered the error.
    pub method: String,
    /// The actual error.
    pub error: String,
}

/// The Java exception reported by the verifier.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct JavaExceptionWithOrigin {
    /// To which method corresponds the program that triggered the exception.
    pub method: String,
    /// The actual exception.
    pub exception: JavaException,
}
