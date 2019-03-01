// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Prusti Interface is an interface between Prusti and Prusti-Viper.

#![deny(unused_must_use)]
#![allow(missing_docs)]
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
extern crate rustc_hash;
extern crate rustc_mir;
extern crate rustc_data_structures;
extern crate rustc_target;
#[macro_use]
extern crate serde_derive;
extern crate serde;
extern crate syntax;
extern crate syntax_pos;
extern crate config as config_crate;
#[macro_use]
extern crate lazy_static;

pub mod environment;
pub mod verifier;
pub mod data;
pub mod constants;
pub mod specifications;
pub mod utils;
pub mod report;
pub mod config;
pub mod parser;
pub mod ast_builder;
pub mod sysroot;
