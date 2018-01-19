// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationResult {
    Success(),
    Failure(Vec<VerificationError>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationError {
    error_type: String,
    pos_id: String,
}

impl VerificationError {
    pub fn new(error_type: String, pos_id: String) -> Self {
        VerificationError { error_type, pos_id }
    }
}
