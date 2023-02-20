// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[macro_export]
macro_rules! error_internal {
    ($span:expr => $message:expr) => {
        return Err($crate::encoder::errors::SpannedEncodingError::internal($message, $span))
    };
    ($span:expr => $($tokens:tt)+) => {
        return Err($crate::encoder::errors::SpannedEncodingError::internal(format!($($tokens)+), $span))
    };
    ($message:expr) => {
        return Err($crate::encoder::errors::EncodingError::internal($message))
    };
    ($($tokens:tt)+) => {
        return Err($crate::encoder::errors::EncodingError::internal(format!($($tokens)+)))
    };
}

#[macro_export]
macro_rules! error_incorrect {
    ($span:expr => $message:expr) => {
        return Err($crate::encoder::errors::SpannedEncodingError::incorrect($message, $span))
    };
    ($span:expr => $($tokens:tt)+) => {
        return Err($crate::encoder::errors::SpannedEncodingError::incorrect(format!($($tokens)+), $span))
    };
    ($message:expr) => {
        return Err($crate::encoder::errors::EncodingError::incorrect($message))
    };
    ($($tokens:tt)+) => {
        return Err($crate::encoder::errors::EncodingError::incorrect(format!($($tokens)+)))
    };
}

#[macro_export]
macro_rules! error_unsupported {
    ($span:expr => $message:expr) => {
        return Err($crate::encoder::errors::SpannedEncodingError::unsupported($message, $span))
    };
    ($span:expr => $($tokens:tt)+) => {
        return Err($crate::encoder::errors::SpannedEncodingError::unsupported(format!($($tokens)+), $span))
    };
    ($message:expr) => {
        return Err($crate::encoder::errors::EncodingError::unsupported($message))
    };
    ($($tokens:tt)+) => {
        return Err($crate::encoder::errors::EncodingError::unsupported(format!($($tokens)+)))
    };
}
