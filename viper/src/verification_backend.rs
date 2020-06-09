// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub enum VerificationBackend {
    Silicon,
    Carbon,
}

impl VerificationBackend {
    pub fn from_str(backend: &str) -> Self {
        match backend.to_lowercase().as_str() {
            "silicon" => VerificationBackend::Silicon,
            "carbon" => VerificationBackend::Carbon,
            _ => panic!(
                "Invalid verification backend: '{}'. Allowed values are 'Silicon' and 'Carbon'",
                backend
            ),
        }
    }
}

impl fmt::Display for VerificationBackend {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &VerificationBackend::Silicon => write!(f, "Silicon"),
            &VerificationBackend::Carbon => write!(f, "Carbon"),
        }
    }
}
