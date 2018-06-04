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
    error_full_id: String,
    pos_id: String,
    readable_message: String
}

impl VerificationError {
    pub fn new(error_full_id: String, pos_id: String, readable_message: String) -> Self {
        VerificationError { error_full_id, pos_id, readable_message }
    }

    pub fn get_full_id(&self) -> String {
        self.error_full_id.clone()
    }

    pub fn get_pos_id(&self) -> String {
        self.pos_id.clone()
    }
}
