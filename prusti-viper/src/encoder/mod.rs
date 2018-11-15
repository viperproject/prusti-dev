// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

pub use self::encoder::Encoder;

mod encoder;
mod builtin_encoder;
mod procedure_encoder;
mod loop_encoder;
mod mir_encoder;
mod pure_function_encoder;
mod mir_interpreter;
mod spec_encoder;
mod borrows;
mod type_encoder;
mod utils;
mod places;
mod foldunfold;
mod error_manager;
mod optimiser;

pub mod vir;

