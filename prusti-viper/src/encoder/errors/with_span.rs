// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_span::MultiSpan;
use crate::encoder::errors::{SpannedEncodingError, EncodingError};
use log::trace;

/// Helper trait to convert a `Result<T, EncodingError>` to a
/// `Result<T, SpannedEncodingError>`.
pub trait WithSpan<T> {
    fn with_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError>;
    fn with_default_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError>;
}

impl<T> WithSpan<T> for Result<T, EncodingError> {
    fn with_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError> {
        self.map_err(|err| {
            trace!("Converting a EncodingError to SpannedEncodingError in a Result");
            err.with_span(span)
        })
    }
    fn with_default_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError> {
        self.map_err(|err| {
            trace!("Converting a EncodingError to SpannedEncodingError in a Result");
            err.with_default_span(span)
        })
    }
}

impl<T> WithSpan<T> for Result<T, SpannedEncodingError> {
    fn with_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, SpannedEncodingError> {
        self.map_err(|err| {
            trace!("Replacing the span of an SpannedEncodingError in a Result");
            err.with_span(span)
        })
    }
    fn with_default_span<S: Into<MultiSpan>>(self, _span: S) -> Result<T, SpannedEncodingError> {
        trace!("Ignoring the span because the error already has one.");
        self
    }
}
