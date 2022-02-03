// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Prusti Interface is an interface between Prusti and Prusti-Viper.

#![deny(unused_must_use)]
#![deny(unsafe_op_in_unsafe_fn)]

#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]
#![feature(control_flow_enum)]

// #![feature(nll)]

// #![feature(try_from)]
// #![feature(crate_in_paths)]
// #![feature(map_get_key_value)]

extern crate config as config_crate;
extern crate rustc_borrowck;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_ast;
extern crate rustc_attr;
extern crate rustc_data_structures;
extern crate rustc_index;
extern crate rustc_trait_selection;
extern crate polonius_engine;
extern crate rustc_mir_dataflow;
extern crate rustc_errors;
extern crate rustc_infer;
extern crate rustc_target;
extern crate tracing;
extern crate lazy_static;

pub mod data;
pub mod environment;
pub mod specs;
pub mod utils;

pub use prusti_error::*;

mod prusti_error;
