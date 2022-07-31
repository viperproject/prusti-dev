// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod packup;
mod unify;

pub use packup::*;
pub use unify::*;

use crate::syntax::MicroMirStatement;

/// Represents any transformation of the free PCS we are permitted to do
pub trait Repacking<'tcx> {
    /// Transform the repacking into a sequence of MicroMir statements
    fn encode(&self) -> Vec<MicroMirStatement<'tcx>>;
}
