// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![deny(unused_imports)]
#![deny(dead_code)]
#![deny(warnings)]
#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]

extern crate env_logger;
#[macro_use]
extern crate log;
extern crate rustc;
extern crate syntax;

extern crate serde;
#[macro_use]
extern crate serde_derive;

extern crate prusti_interface;

pub mod validators;
