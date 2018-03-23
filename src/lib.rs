// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Prusti Interface is an interface between Prusti and Prusti-Viper.

#![warn(missing_docs)]
#![feature(rustc_private)]

#[macro_use]
extern crate log;
extern crate rustc;

pub mod environment;
pub mod verifier;
pub mod data;
