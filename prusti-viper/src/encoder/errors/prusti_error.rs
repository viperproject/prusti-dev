// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use syntax_pos::MultiSpan;
use prusti_interface::environment::Environment;

/// The Prusti error that will be reported to the user.
///
/// A Prusti error can originate from:
/// * an encoding error (see the `EncodingError` type)
/// * a Viper verification error
#[derive(Clone, Debug)]
pub struct PrustiError {
    message: String,
    span: MultiSpan,
    help: Option<String>,
    note: Option<(String, MultiSpan)>,
}

impl PrustiError {
    /// Private constructor. Use one of the following methods.
    fn new(message: String, span: MultiSpan) -> Self {
        PrustiError {
            message,
            span,
            help: None,
            note: None,
        }
    }

    /// Report a verification error of the verified Rust code
    pub fn verification<S: ToString>(message: S, span: MultiSpan) -> Self {
        PrustiError::new(format!("[Prusti verification error] {}", message.to_string()), span)
    }

    /// Report an unsupported feature of the verified Rust code (e.g. dereferencing raw pointers)
    pub fn unsupported<S: ToString>(message: S, span: MultiSpan) -> Self {
        PrustiError::new(format!("[Prusti unsupported feature] {}", message.to_string()), span)
    }

    /// Report an incorrect usage of Prusti (e.g. call an impure function in a contract)
    pub fn incorrect<S: ToString>(message: S, span: MultiSpan) -> Self {
        PrustiError::new(format!("[Prusti invalid specification] {}", message.to_string()), span)
    }

    /// Report an internal error of Prusti (e.g. failure of the fold-unfold)
    pub fn internal<S: ToString>(message: S, span: MultiSpan) -> Self {
        PrustiError::new(format!("[Prusti internal error] {}", message.to_string()), span)
    }

    pub fn set_help<S: ToString>(mut self, message: S) -> Self {
        self.help = Some(message.to_string());
        self
    }

    /// Report the error using the compiler's interface
    pub fn emit(self, env: &Environment) {
        env.span_err_with_help_and_note(
            self.span,
            &self.message,
            &self.help,
            &self.note,
        );
    }

    /// Set the span of the failing assertion expression.
    ///
    /// Note: this is a noop if `opt_span` is None
    pub fn set_failing_assertion(mut self, opt_span: Option<&MultiSpan>) -> Self {
        if let Some(span) = opt_span {
            self.note = Some(("the failing assertion is here".to_string(), span.clone()));
        }
        self
    }

    /// Convert the original error span to a note, and add a new error span.
    ///
    /// Note: this is a noop if `opt_span` is None
    pub fn push_primary_span(mut self, opt_span: Option<&MultiSpan>) -> Self {
        if let Some(span) = opt_span {
            self.note = Some(("the error originates here".to_string(), self.span));
            self.span = span.clone();
        }
        self
    }
}
