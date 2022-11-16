// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![feature(rustc_private)]
#![feature(box_patterns)]

pub mod abstract_interpretation;
mod analysis_error;
pub mod domains;
pub mod mir_utils;
mod pointwise_state;

pub use analysis_error::AnalysisError;
pub use pointwise_state::PointwiseState;
