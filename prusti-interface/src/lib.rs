// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Prusti Interface is an interface between Prusti and Prusti-Viper.

#![deny(unused_must_use)]
#![deny(unsafe_op_in_unsafe_fn)]
#![warn(clippy::disallowed_types)]
#![allow(clippy::nonminimal_bool)]
#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(control_flow_enum)]
#![feature(min_specialization)]
// We may want to remove this in the future.
#![allow(clippy::needless_lifetimes)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

pub mod data;
pub mod environment;
pub mod specs;
pub mod utils;

pub use prusti_error::*;

mod prusti_error;
