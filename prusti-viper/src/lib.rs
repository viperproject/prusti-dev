// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(try_blocks)]
#![feature(never_type)]
#![feature(btree_extract_if)]
#![feature(decl_macro)]
#![feature(extract_if)]
#![feature(let_chains)]
#![feature(type_changing_struct_update)]
#![deny(unused_must_use)]
#![deny(unreachable_patterns)]
#![warn(clippy::disallowed_types)]
// This Clippy check seems to be always wrong.
#![allow(clippy::iter_with_drain)]
// We may want to remove this in the future.
#![allow(clippy::needless_lifetimes)]
#![allow(clippy::needless_pass_by_ref_mut)] // see https://github.com/rust-lang/rust-clippy/issues/11179

pub mod encoder;
mod utils;
pub mod verifier;
