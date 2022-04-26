// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_span::{Span, MultiSpan};
use crate::environment::Environment;
use prusti_common::config;
use ::log::warn;

/// The Prusti message that will be reported to the user.
///
/// A Prusti message can originate from:
/// * invalid usage detected during specification collection
/// * an encoding error (see the `SpannedEncodingError` type)
/// * a Viper verification error
///
/// A `PrustiError` can be displayed as a *warning* to the user. (We should rename `PrustiError`,
/// `SpannedEncodingError` and similar types to something less confusing.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrustiError {
    is_error: bool,
    /// If `true`, it should not be reported to the user. We need this in cases
    /// when the same error could be reported twice.
    ///
    /// FIXME: This is a workaround: we get duplicate errors because we
    /// currently verify functions multiple times. Once this is fixed, this
    /// field should be removed.
    is_disabled: bool,
    message: String,
    span: MultiSpan,
    help: Option<String>,
    notes: Vec<(String, Option<MultiSpan>)>,
}

impl PartialOrd for PrustiError {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.span.primary_span().partial_cmp(&other.span.primary_span())
    }
}

impl Ord for PrustiError {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl PrustiError {
    /// Private constructor. Use one of the following methods.
    fn new(message: String, span: MultiSpan) -> Self {
        PrustiError {
            is_error: true,
            is_disabled: false,
            message,
            span,
            help: None,
            notes: vec![],
        }
    }

    /// Report a verification error of the verified Rust code
    pub fn verification<S: ToString>(message: S, span: MultiSpan) -> Self {
        check_message(message.to_string());
        PrustiError::new(
            format!("[Prusti: verification error] {}", message.to_string()),
            span
        )
    }

    pub fn disabled_verification<S: ToString>(message: S, span: MultiSpan) -> Self {
        check_message(message.to_string());
        let mut error = PrustiError::new(
            format!("[Prusti: verification error] {}", message.to_string()),
            span
        );
        error.is_disabled = true;
        error
    }

    /// Report an unsupported feature of the verified Rust code (e.g. dereferencing raw pointers)
    pub fn unsupported<S: ToString>(message: S, span: MultiSpan) -> Self {
        check_message(message.to_string());
        let mut error = PrustiError::new(
            format!("[Prusti: unsupported feature] {}", message.to_string()),
            span
        );
        if config::skip_unsupported_features() {
            error.set_warning();
        }
        error
    }

    /// Report an incorrect usage of Prusti (e.g. call an impure function in a contract)
    pub fn incorrect<S: ToString>(message: S, span: MultiSpan) -> Self {
        check_message(message.to_string());
        PrustiError::new(
            format!("[Prusti: invalid specification] {}", message.to_string()),
            span
        )
    }

    /// Report an internal error of Prusti (e.g. failure of the fold-unfold)
    pub fn internal<S: ToString>(message: S, span: MultiSpan) -> Self {
        check_message(message.to_string());
        let mut error = PrustiError::new(
            "[Prusti internal error] Prusti encountered an unexpected internal error".to_string(),
            span
        ).add_note(
            "We would appreciate a bug report: https://github.com/viperproject/prusti-dev/issues/new",
            None
        ).add_note(
            format!("Details: {}", message.to_string()),
            None
        );
        if config::internal_errors_as_warnings() {
            error.set_warning();
        }
        error
    }

    /// Set that this Prusti error should be reported as a warning to the user
    pub fn set_warning(&mut self) {
        self.is_error = false;
    }

    pub fn is_error(&self) -> bool {
        self.is_error
    }

    // FIXME: This flag is a temporary workaround for having duplicate errors
    // coming from verifying functions multiple times. We should verify each
    // function only once.
    pub fn is_disabled(&self) -> bool {
        self.is_disabled
    }

    #[must_use]
    pub fn set_help<S: ToString>(mut self, message: S) -> Self {
        self.help = Some(message.to_string());
        self
    }

    #[must_use]
    pub fn add_note<S: ToString>(mut self, message: S, opt_span: Option<Span>) -> Self {
        self.notes.push((message.to_string(), opt_span.map(MultiSpan::from)));
        self
    }

    pub fn add_note_mut<S: ToString>(&mut self, message: S, opt_span: Option<MultiSpan>) {
        self.notes.push((message.to_string(), opt_span));
    }

    /// Report the encoding error using the compiler's interface
    pub fn emit(self, env: &Environment) {
        assert!(!self.is_disabled);
        if self.is_error {
            env.span_err_with_help_and_notes(
                self.span,
                &self.message,
                &self.help,
                &self.notes,
            );
        } else {
            env.span_warn_with_help_and_notes(
                self.span,
                &self.message,
                &self.help,
                &self.notes,
            );
        }
    }

    /// Cancel the error.
    pub fn cancel(self) {
        assert!(self.is_disabled);
    }

    /// Set the span of the failing assertion expression.
    ///
    /// Note: this is a noop if `opt_span` is None
    #[must_use]
    pub fn set_failing_assertion(mut self, opt_span: Option<&MultiSpan>) -> Self {
        if let Some(span) = opt_span {
            let note = "the failing assertion is here".to_string();
            self.notes.push((note, Some(span.clone())));
        }
        self
    }

    /// Convert the original error span to a note, and add a new error span.
    ///
    /// Note: this is a noop if `opt_span` is None
    #[must_use]
    pub fn push_primary_span(mut self, opt_span: Option<&MultiSpan>) -> Self {
        if let Some(span) = opt_span {
            self.notes.push(("the error originates here".to_string(), Some(self.span)));
            self.span = span.clone();
        }
        self
    }
}

fn check_message(message: String) {
    debug_assert!(
        message.len() >= 3,
        "Message {:?} is too short",
        message
    );
    if message.get(0..1).unwrap() != message.get(0..1).unwrap().to_lowercase() {
        warn!("Message {:?} should start with a lowercase character", message);
    }
}
