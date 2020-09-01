// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns)]
// #![feature(nll)]
#![feature(box_syntax)]
// #![feature(slice_sort_by_cached_key)]
// #![feature(iterator_flatten)]

#![allow(warnings)]

// #![deny(unreachable_patterns)]
// #![deny(unused_mut)]
// #![deny(unused_variables)]
// #![deny(unused_imports)]
// #![deny(unused_doc_comments)]

extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_span;
extern crate rustc_index;
extern crate rustc_ast;
extern crate rustc_target;
extern crate rustc_attr;
// #[macro_use]
// extern crate log;
// extern crate num_rational;
// extern crate num_traits;
// extern crate prusti_filter;
// extern crate prusti_interface;
// extern crate regex;
// extern crate rustc;
// extern crate rustc_data_structures;
// extern crate rustc_mir;
// extern crate syntax;
// extern crate syntax_pos;
// extern crate uuid;
// extern crate viper;
#[macro_use]
extern crate lazy_static;

// #[cfg(debug_assertions)]
// #[macro_use]
// extern crate pretty_assertions;

pub mod encoder;
mod utils;
pub mod verifier;
