// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_span::MultiSpan;
use crate::encoder::errors::{EncodingError, PositionlessEncodingError};
use log::trace;

/// Helper trait to run a function in case of error.
pub trait RunIfErr {
    fn run_if_err<F: Fn() -> ()>(self, f: F) -> Self;
}

impl<T> RunIfErr for Result<T, EncodingError> {
    fn run_if_err<F: Fn() -> ()>(self, f: F) -> Self {
        self.map_err(|err| { f(); err })
    }
}

impl<T> RunIfErr for Result<T, PositionlessEncodingError> {
    fn run_if_err<F: Fn() -> ()>(self, f: F) -> Self {
        self.map_err(|err| { f(); err })
    }
}
