// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_span::MultiSpan;
use crate::encoder::errors::{EncodingError, PositionlessEncodingError};
use log::trace;

/// Helper trait to convert a `Result<T, PositionlessEncodingError>` to a
/// `Result<T, EncodingError>`.
pub trait WithSpan<T> {
    fn with_span<S: Into<MultiSpan>>(self, span: S) -> Result<T, EncodingError>;
}

impl<T> WithSpan<T> for Result<T, PositionlessEncodingError> {
    fn with_span<S: Into<MultiSpan>>(self, span: S)
        -> Result<T, EncodingError>
    {
        trace!("Converting a PositionlessEncodingError to EncodingError in a Result");
        self.map_err(|err| err.with_span(span))
    }
}
