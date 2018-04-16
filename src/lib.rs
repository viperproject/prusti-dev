// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Prusti Interface is an interface between Prusti and Prusti-Viper.

#![warn(missing_docs)]
#![feature(rustc_private)]
#![feature(box_syntax)]

#[macro_use]
extern crate log;
#[macro_use]
extern crate lazy_static;
extern crate rustc;
extern crate syntax;
extern crate rustc_driver;
extern crate rustc_mir;
extern crate rustc_data_structures;

pub mod environment;
pub mod verifier;
pub mod data;
pub mod constants;
