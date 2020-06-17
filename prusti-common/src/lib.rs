// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(slice_sort_by_cached_key)]

#[macro_use]
extern crate log;
extern crate config as config_crate;
extern crate serde;
extern crate walkdir;
#[macro_use]
extern crate lazy_static;
extern crate regex;
extern crate uuid;
extern crate viper;

pub mod config;
mod utils;
pub mod vir;
