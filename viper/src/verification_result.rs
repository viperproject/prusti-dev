// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use silicon_counterexample::SiliconCounterexample;
use JavaException;

/// The result of a verification request on a Viper program.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, Default)]
pub struct ProgramVerificationResult {
    /// The errors reported by the verification.
    pub verification_errors: Vec<VerificationError>,
    /// The consistency errors reported by the verifier.
    pub consistency_errors: Vec<ConsistencyError>,
    /// Java exceptions raised by the verifier.
    pub java_exceptions: Vec<JavaExceptionWithOrigin>,
}

/// The result of a verification request on a Viper method.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct VerificationError {
    pub full_id: String,
    pub pos_id: Option<String>,
    pub reason_pos_id: Option<String>,
    pub message: String,
    pub counterexample: Option<SiliconCounterexample>,
}

impl VerificationError {
    pub fn new(
        full_id: String,
        pos_id: Option<String>,
        reason_pos_id: Option<String>,
        message: String,
        counterexample: Option<SiliconCounterexample>,
    ) -> Self {
        VerificationError {
            full_id,
            pos_id,
            reason_pos_id,
            message,
            counterexample,
        }
    }
}

/// The consistency error reported by the verifier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsistencyError {
    /// To which method corresponds the program that triggered the error.
    pub method: String,
    /// The actual error.
    pub error: String,
}

/// The Java exception reported by the verifier.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct JavaExceptionWithOrigin {
    /// To which method corresponds the program that triggered the exception.
    pub method: String,
    /// The actual exception.
    pub exception: JavaException,
}
