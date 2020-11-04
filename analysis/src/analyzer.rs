// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::ty::TyCtxt;
use rustc_middle::mir;
pub use crate::PointwiseState;
pub use crate::AnalysisError;
pub use crate::abstract_domains::*;

type AnalysisResult<T> = std::result::Result<T, AnalysisError>;

pub struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Analyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Analyzer {
            tcx,
        }
    }

    pub fn liveness_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> AnalysisResult<PointwiseState<LivenessState>> {
        unimplemented!();
    }

    pub fn definitely_initialized_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> AnalysisResult<PointwiseState<DefinitelyInitializedState>> {
        unimplemented!();
    }

    pub fn pcs_analysis(
        &self,
        mir: &mir::Body<'tcx>,
    ) -> AnalysisResult<PointwiseState<PCSState>> {
        unimplemented!();
    }
}
