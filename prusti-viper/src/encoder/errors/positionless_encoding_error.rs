// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::errors::EncodingError;
use rustc_span::MultiSpan;
use log::trace;

/// An error in the encoding with no information regarding the source code span.
/// This type is meant to be translated to `EncodingError` as soon as possible.
#[derive(Clone, Debug)]
pub enum PositionlessEncodingError {
    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    Unsupported(String),
    /// Report an incorrect usage of Prusti (e.g. call an impure function in a contract)
    Incorrect(String),
    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    Internal(String),
}

impl PositionlessEncodingError {
    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    pub fn unsupported<M: ToString>(message: M) -> Self {
        PositionlessEncodingError::Unsupported(message.to_string())
    }

    /// Report an incorrect usage of Prusti (e.g. call an impure function in a contract)
    pub fn incorrect<M: ToString>(message: M) -> Self {
        PositionlessEncodingError::Incorrect(message.to_string())
    }

    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    pub fn internal<M: ToString>(message: M) -> Self {
        PositionlessEncodingError::Internal(message.to_string())
    }

    pub fn with_span<S: Into<MultiSpan>>(self, span: S) -> EncodingError {
        match self {
            PositionlessEncodingError::Unsupported(msg) => {
                EncodingError::unsupported(msg, span)
            }
            PositionlessEncodingError::Incorrect(msg) => {
                EncodingError::incorrect(msg, span)
            }
            PositionlessEncodingError::Internal(msg) => {
                EncodingError::internal(msg, span)
            }
        }
    }
}

/// Lossy conversion
impl From<EncodingError> for PositionlessEncodingError {
    fn from(other: EncodingError) -> Self {
        trace!("Converting a EncodingError to PositionlessEncodingError");
        other.error
    }
}
