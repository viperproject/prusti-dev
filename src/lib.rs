// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![recursion_limit = "1024"]

#[macro_use]
extern crate error_chain;
extern crate jni;
#[macro_use]
extern crate log;
extern crate uuid;
extern crate viper_sys;

mod viper;
mod verification_context;
mod ast_factory;
mod verification_result;
mod verifier;
mod jni_utils;
mod ast_utils;
pub mod errors;
pub mod utils;

pub use viper::*;
pub use verifier::*;
pub use verification_context::*;
pub use ast_factory::*;
pub use verification_result::*;
pub use ast_utils::*;
