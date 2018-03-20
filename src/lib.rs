// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]

#[macro_use]
extern crate log;
extern crate prusti_interface;
extern crate viper;
extern crate rustc;

mod procedures_table;
mod fields_table;
pub mod verifier;
