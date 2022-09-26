// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(box_patterns)]
#![feature(box_syntax)]
#![deny(unused_must_use)]

pub mod config;
pub mod launch;
pub mod report;
mod stopwatch;
pub mod utils;

pub use stopwatch::Stopwatch;
