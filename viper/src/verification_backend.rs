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

#[derive(Clone, Debug)]
pub struct UknownBackendError(String);

impl fmt::Display for UknownBackendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Invalid verification backend: '{}'. Allowed values are 'Silicon' and 'Carbon'",
            self.0
        )
    }
}

impl std::str::FromStr for VerificationBackend {
    type Err = UknownBackendError;
    fn from_str(backend: &str) -> Result<Self, Self::Err> {
        match backend.to_lowercase().as_str() {
            "silicon" => Ok(VerificationBackend::Silicon),
            "carbon" => Ok(VerificationBackend::Carbon),
            _ => Err(UknownBackendError(backend.to_string())),
        }
    }
}

impl fmt::Display for VerificationBackend {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            VerificationBackend::Silicon => write!(f, "Silicon"),
            VerificationBackend::Carbon => write!(f, "Carbon"),
        }
    }
}
