// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{AbstractState, AnalysisError};
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;

pub struct PCSState {}
impl<'tcx> AbstractState<'tcx> for PCSState {
    fn new_bottom(mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        unimplemented!()
    }

    fn new_initial(mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        unimplemented!()
    }

    fn need_to_widen(counter: &u32) -> bool {
        unimplemented!()
    }

    fn join(&mut self, other: &Self) {
        unimplemented!()
    }

    fn widen(&mut self, previous: &Self) {
        unimplemented!()
    }

    fn apply_statement_effect(&mut self, location: &mir::Location, mir: &mir::Body<'tcx>)
    -> Result<(), AnalysisError> {
        unimplemented!()
    }

    fn apply_terminator_effect(&self, location: &mir::Location, mir: &mir::Body<'tcx>)
        -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        unimplemented!()
    }
}
