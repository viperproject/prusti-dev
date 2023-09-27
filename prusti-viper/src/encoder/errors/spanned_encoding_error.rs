// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::{debug, error};
use prusti_interface::PrustiError;
use prusti_rustc_interface::errors::MultiSpan;

use crate::encoder::errors::EncodingErrorKind;
use backtrace::Backtrace;

/// An error in the encoding with information regarding the source code span that caused it.
#[derive(Clone, Debug)]
pub struct SpannedEncodingError {
    pub(super) error: EncodingErrorKind,
    span: Box<MultiSpan>,
    help: Option<String>,
    notes: Vec<(String, Option<MultiSpan>)>,
}

pub type SpannedEncodingResult<T> = Result<T, SpannedEncodingError>;

impl From<SpannedEncodingError> for PrustiError {
    fn from(other: SpannedEncodingError) -> Self {
        let mut error = match other.error {
            EncodingErrorKind::Unsupported(msg) => PrustiError::unsupported(msg, *other.span),
            EncodingErrorKind::Incorrect(msg) => PrustiError::incorrect(msg, *other.span),
            EncodingErrorKind::Internal(msg) => PrustiError::internal(msg, *other.span),
        };
        if let Some(help) = other.help {
            error = error.set_help(help);
        }
        for (message, span) in other.notes {
            error.add_note_mut(message, span);
        }
        error
    }
}

impl SpannedEncodingError {
    pub(super) fn new<S: Into<MultiSpan>>(error: EncodingErrorKind, span: S) -> Self {
        SpannedEncodingError {
            error,
            span: Box::new(span.into()),
            help: None,
            notes: Vec::new(),
        }
    }

    /// Usage of an unsupported Rust feature (e.g. dereferencing raw pointers)
    #[tracing::instrument(level = "debug", skip(message, span))]
    pub fn unsupported<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        if cfg!(debug_assertions) {
            debug!("Constructing unsupported error at:\n{:?}", Backtrace::new());
        }
        SpannedEncodingError::new(EncodingErrorKind::unsupported(message), span)
    }

    /// An incorrect usage of Prusti (e.g. call an impure function in a contract)
    #[tracing::instrument(level = "debug", skip(message, span))]
    pub fn incorrect<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        if cfg!(debug_assertions) {
            debug!("Constructing incorrect error at:\n{:?}", Backtrace::new());
        }
        SpannedEncodingError::new(EncodingErrorKind::incorrect(message), span)
    }

    /// An internal error of Prusti (e.g. failure of the fold-unfold)
    pub fn internal<M: ToString, S: Into<MultiSpan>>(message: M, span: S) -> Self {
        if cfg!(debug_assertions) {
            error!("Constructing internal error at:\n{:?}", Backtrace::new());
        }
        SpannedEncodingError::new(EncodingErrorKind::internal(message), span)
    }

    pub fn kind(&self) -> &EncodingErrorKind {
        &self.error
    }

    pub fn with_span<S: Into<MultiSpan>>(mut self, span: S) -> SpannedEncodingError {
        // TODO: Stack error spans
        *self.span = span.into();
        self
    }

    pub fn add_note<S: ToString>(&mut self, message: S, opt_span: Option<MultiSpan>) {
        self.notes.push((message.to_string(), opt_span));
    }

    pub fn set_help<S: ToString>(&mut self, message: S) {
        self.help = Some(message.to_string());
    }
}
