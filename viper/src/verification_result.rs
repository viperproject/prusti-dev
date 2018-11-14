// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerificationResult {
    Success(),
    Failure(Vec<VerificationError>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VerificationError {
    pub full_id: String,
    pub pos_id: Option<String>,
    pub message: String
}

impl VerificationError {
    pub fn new(full_id: String, pos_id: Option<String>, message: String) -> Self {
        VerificationError { full_id, pos_id, message }
    }
}
