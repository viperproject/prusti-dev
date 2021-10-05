// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_span::MultiSpan;
use log::debug;
use prusti_interface::PrustiError;
use crate::encoder::errors::EncodingError;
use crate::encoder::errors::EncodingErrorKind;
use backtrace::Backtrace;

/// An error in the encoding with information regarding the source code span that caused it.
#[derive(Clone, Debug)]
pub struct SpannedEncodingError {
    pub(super) error: EncodingErrorKind,
    span: MultiSpan,
}

pub type SpannedEncodingResult<T> = Result<T, SpannedEncodingError>;

impl From<SpannedEncodingError> for PrustiError {
    fn from(other: SpannedEncodingError) -> Self {
        match other.error {
            EncodingErrorKind::Unsupported(msg) => {
                PrustiError::unsupported(msg, other.span)
            }
            EncodingErrorKind::Incorrect(msg) => {
                PrustiError::incorrect(msg, other.span)
            }
            EncodingErrorKind::Internal(msg) => {
                PrustiError::internal(msg, other.span)
            }
        }
    }
}

impl SpannedEncodingError {
    pub(super) fn new<S: Into<MultiSpan>>(error: EncodingErrorKind, span: S) -> Self {
        SpannedEncodingError {
            error,
            span: span.into(),
        }
    }

    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    pub fn unsupported<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        debug!("Constructing unsupported error at:\n{:?}", Backtrace::new());
        SpannedEncodingError::new(
            EncodingErrorKind::unsupported(message),
            span
        )
    }

    /// An incorrect usage of Prusti (e.g. call an impure function in a contract)
    pub fn incorrect<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        debug!("Constructing incorrect error at:\n{:?}", Backtrace::new());
        SpannedEncodingError::new(
            EncodingErrorKind::incorrect(message),
            span
        )
    }

    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    pub fn internal<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        debug!("Constructing internal error at:\n{:?}", Backtrace::new());
        SpannedEncodingError::new(
            EncodingErrorKind::internal(message),
            span
        )
    }

    pub fn kind(&self) -> &EncodingErrorKind {
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
