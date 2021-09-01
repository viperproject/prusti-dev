// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{AbstractState, AnalysisError};
use rustc_middle::{mir, ty::TyCtxt};
use serde::{Serialize, Serializer};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct PCSState {}

#[allow(unused_variables)]
impl Serialize for PCSState {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        unimplemented!()
    }
}

#[allow(unused_variables)]
impl<'a, 'tcx: 'a> AbstractState<'a, 'tcx> for PCSState {
    fn new_bottom(mir: &'a mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        unimplemented!()
    }

    fn is_bottom(&self) -> bool {
        unimplemented!()
    }

    fn new_initial(mir: &'a mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
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

    fn apply_statement_effect(&mut self, location: mir::Location) -> Result<(), AnalysisError> {
        unimplemented!()
    }

    fn apply_terminator_effect(
        &self,
        location: mir::Location,
    ) -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        unimplemented!()
    }
}
