// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(nll)]
#![feature(box_syntax)]
#![feature(slice_sort_by_cached_key)]
#![feature(custom_attribute)]
#![deny(unreachable_patterns)]
#![cfg_attr(debug_assertions, deny(dead_code))]
#![deny(unused_mut)]
#![deny(unused_variables)]
#![deny(unused_imports)]
#![deny(unused_doc_comments)]

#[macro_use]
extern crate log;
extern crate num_rational;
extern crate num_traits;
extern crate prusti_filter;
#[macro_use]
extern crate prusti_interface;
extern crate regex;
extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_mir;
extern crate syntax;
extern crate syntax_pos;
extern crate uuid;
extern crate viper;
#[macro_use]
extern crate lazy_static;
extern crate serde;
extern crate serde_json;
#[macro_use]
extern crate serde_derive;

#[cfg(debug_assertions)]
#[macro_use]
extern crate pretty_assertions;

pub mod encoder;
mod utils;
pub mod verifier;
pub mod verification_service;
