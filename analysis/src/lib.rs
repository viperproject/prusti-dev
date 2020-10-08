// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]

extern crate rustc_middle;

mod pointwise_state;
mod abstract_state;
mod analysis_error;
mod analyzer;
pub mod abstract_domains;

use rustc_middle::ty::TyCtxt;
use rustc_middle::mir;
pub use pointwise_state::PointwiseState;
pub use abstract_state::AbstractState;
pub use analysis_error::AnalysisError;
pub use analyzer::Analyzer;
