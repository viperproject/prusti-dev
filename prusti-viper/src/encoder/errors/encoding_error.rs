// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::errors::{EncodingErrorKind, SpannedEncodingError};
use backtrace::Backtrace;
use log::{debug, error};
use prusti_rustc_interface::errors::MultiSpan;

/// An error in the encoding with *optional* information regarding the source code span.
#[derive(Clone, Debug)]
pub enum EncodingError {
    Positionless(EncodingErrorKind),
    Spanned(SpannedEncodingError),
}

pub type EncodingResult<T> = Result<T, EncodingError>;

impl EncodingError {
    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    #[tracing::instrument(level = "debug", skip(message))]
    pub fn unsupported<M: ToString>(message: M) -> Self {
        if cfg!(debug_assertions) {
            debug!("Constructing unsupported error at:\n{:?}", Backtrace::new());
        }
        EncodingError::Positionless(EncodingErrorKind::unsupported(message))
    }

    /// An incorrect usage of Prusti (e.g. call an impure function in a contract)
    #[tracing::instrument(level = "debug", skip(message))]
    pub fn incorrect<M: ToString>(message: M) -> Self {
        if cfg!(debug_assertions) {
            debug!("Constructing incorrect error at:\n{:?}", Backtrace::new());
        }
        EncodingError::Positionless(EncodingErrorKind::incorrect(message))
    }

    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    #[tracing::instrument(level = "error", skip(message))]
    pub fn internal<M: ToString>(message: M) -> Self {
        if cfg!(debug_assertions) {
            error!("Constructing internal error at:\n{:?}", Backtrace::new());
        }
        EncodingError::Positionless(EncodingErrorKind::internal(message))
    }

    pub fn kind(&self) -> &EncodingErrorKind {
        match self {
            EncodingError::Positionless(error) => error,
            EncodingError::Spanned(error) => error.kind(),
        }
    }

    pub fn with_span<S: Into<MultiSpan>>(self, span: S) -> SpannedEncodingError {
        match self {
            EncodingError::Positionless(error) => SpannedEncodingError::new(error, span),
            EncodingError::Spanned(error) => error.with_span(span),
        }
    }

    pub fn with_default_span<S: Into<MultiSpan>>(self, span: S) -> SpannedEncodingError {
        match self {
            EncodingError::Positionless(error) => SpannedEncodingError::new(error, span),
            EncodingError::Spanned(error) => error,
        }
    }
}

impl From<SpannedEncodingError> for EncodingError {
    fn from(other: SpannedEncodingError) -> Self {
        EncodingError::Spanned(other)
    }
}
