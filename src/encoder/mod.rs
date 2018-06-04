// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod encoder;
mod procedure_encoder;
mod loop_encoder;
mod borrows;
mod type_encoder;
mod utils;
mod places;
mod foldunfold;
mod error_manager;

pub mod vir;

pub use self::encoder::Encoder;
