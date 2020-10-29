// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::PrustiError;
use rustc_span::MultiSpan;
use crate::encoder::errors::PositionlessEncodingError;

/// An error in the encoding
#[derive(Clone, Debug)]
pub struct EncodingError {
    pub(super) error: PositionlessEncodingError,
    span: MultiSpan,
}

impl Into<PrustiError> for EncodingError {
    fn into(self) -> PrustiError {
        match self.error {
            PositionlessEncodingError::Unsupported(msg) => {
                PrustiError::unsupported(msg, self.span)
            }
            PositionlessEncodingError::Incorrect(msg) => {
                PrustiError::incorrect(msg, self.span)
            }
            PositionlessEncodingError::Internal(msg) => {
                PrustiError::internal(msg, self.span)
            }
        }
    }
}

impl EncodingError {
    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    pub fn unsupported<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        PositionlessEncodingError::unsupported(message).with_span(span)
    }

    /// Report an incorrect usage of Prusti (e.g. call an impure function in a contract)
    pub fn incorrect<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        PositionlessEncodingError::incorrect(message).with_span(span)
    }

    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    pub fn internal<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        PositionlessEncodingError::internal(message).with_span(span)
    }
}
