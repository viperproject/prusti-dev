// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub use self::encoder::Encoder;

mod builtin_encoder;
#[allow(clippy::module_inception)]
mod encoder;
mod errors;
mod foldunfold;
mod initialisation;
mod interface;
mod loop_encoder;
mod mir_encoder;
mod mir_successor;
mod name_interner;
mod places;
mod procedure_encoder;
mod stub_function_encoder;
mod stub_procedure_encoder;
mod utils;
mod snapshot;
mod mirror_function_encoder;
mod mir;
mod high;
mod typed;
mod middle;
mod purifier;
pub mod counterexamples;
mod definition_collector;
mod versioning;
