// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(try_blocks)]
#![feature(never_type)]
#![feature(btree_drain_filter)]
#![feature(decl_macro)]
#![feature(drain_filter)]

#![deny(unused_must_use)]
#![deny(unreachable_patterns)]
// This Clippy chcek seems to be always wrong.
#![allow(clippy::iter_with_drain)]

pub mod encoder;
mod utils;
pub mod verifier;
