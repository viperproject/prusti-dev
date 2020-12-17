// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::PrustiError;
use rustc_span::MultiSpan;
use crate::encoder::errors::PositionlessEncodingError;

/// An error in the encoding with information regarding the source code span that caused it.
#[derive(Clone, Debug)]
pub struct SpannedEncodingError {
    pub(super) error: PositionlessEncodingError,
    span: MultiSpan,
}

pub type SpannedEncodingResult<T> = Result<T, SpannedEncodingError>;

impl Into<PrustiError> for SpannedEncodingError {
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

impl SpannedEncodingError {
    fn new<S: Into<MultiSpan>>(error: PositionlessEncodingError, span: S) -> Self {
        SpannedEncodingError {
            error,
            span: span.into(),
        }
    }

    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    pub fn unsupported<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        SpannedEncodingError::new(
            PositionlessEncodingError::unsupported(message),
            span
        )
    }

    /// Report an incorrect usage of Prusti (e.g. call an impure function in a contract)
    pub fn incorrect<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        SpannedEncodingError::new(
            PositionlessEncodingError::incorrect(message),
            span
        )
    }

    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    pub fn internal<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        SpannedEncodingError::new(
            PositionlessEncodingError::internal(message),
            span
        )
    }

    pub fn as_positionless(&self) -> &PositionlessEncodingError {
        &self.error
    }

    pub fn with_span<S: Into<MultiSpan>>(self, span: S) -> SpannedEncodingError {
        // TODO: Stack error spans
        SpannedEncodingError {
            span: span.into(),
            ..self
        }
    }
}
