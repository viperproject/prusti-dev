// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// An error in the encoding with no information regarding the source code span.
#[derive(Clone, Debug)]
pub enum EncodingErrorKind {
    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    Unsupported(String),
    /// Report an incorrect usage of Prusti (e.g. call an impure function in a contract)
    Incorrect(String),
    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    Internal(String),
}

impl EncodingErrorKind {
    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    pub fn unsupported<M: ToString>(message: M) -> Self {
        EncodingErrorKind::Unsupported(message.to_string())
    }

    /// An incorrect usage of Prusti (e.g. call an impure function in a contract)
    pub fn incorrect<M: ToString>(message: M) -> Self {
        EncodingErrorKind::Incorrect(message.to_string())
    }

    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    pub fn internal<M: ToString>(message: M) -> Self {
        EncodingErrorKind::Internal(message.to_string())
    }
}
