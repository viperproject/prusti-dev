// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines a replacement for rustc's `ErrorGuaranteed` type.

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ErrorGuaranteed;

impl From<rustc_errors::ErrorGuaranteed> for ErrorGuaranteed {
    fn from(_: rustc_errors::ErrorGuaranteed) -> ErrorGuaranteed {
        ErrorGuaranteed
    }
}
