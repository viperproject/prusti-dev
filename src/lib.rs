// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Prusti Interface is an interface between Prusti and Prusti-Viper.

#![warn(missing_docs)]
#![feature(nll)]
#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]
#![feature(try_from)]
#![feature(crate_in_paths)]

extern crate csv;
extern crate datafrog;
#[macro_use]
extern crate log;
extern crate polonius;
extern crate polonius_engine;
extern crate regex;
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_mir;
extern crate rustc_data_structures;
extern crate serde;
extern crate syntax;
extern crate syntax_pos;

pub mod environment;
pub mod verifier;
pub mod data;
pub mod constants;
pub mod specifications;
pub mod utils;
