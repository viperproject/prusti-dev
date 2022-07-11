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

pub mod data;
pub mod environment;
pub mod specs;
pub mod utils;

pub use prusti_error::*;

mod prusti_error;
