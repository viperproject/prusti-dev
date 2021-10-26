// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{analysis::AnalysisResult, AbstractState, Analysis};
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::def_id::DefId;
use serde::{Serialize, Serializer};

pub struct PCSAnalysis<'mir, 'tcx: 'mir> {
    def_id: DefId,
    mir: &'mir mir::Body<'tcx>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct PCSState {}

impl<'mir, 'tcx: 'mir> PCSAnalysis<'mir, 'tcx> {
    pub fn new(_tcx: TyCtxt<'tcx>, def_id: DefId, mir: &'mir mir::Body<'tcx>) -> Self {
        PCSAnalysis { def_id, mir }
    }
}

impl<'mir, 'tcx: 'mir> Analysis<'mir, 'tcx> for PCSAnalysis<'mir, 'tcx> {
    type State = PCSState;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        self.mir
    }

    fn new_bottom(&self) -> Self::State {
        unimplemented!()
    }

    fn new_initial(&self) -> Self::State {
        unimplemented!()
    }

    fn need_to_widen(_counter: u32) -> bool {
        unimplemented!()
    }

    fn apply_statement_effect(
        &self,
        _state: &mut Self::State,
        _location: mir::Location,
    ) -> AnalysisResult<()> {
        unimplemented!()
    }

    fn apply_terminator_effect(
        &self,
        _state: &Self::State,
        _location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        unimplemented!()
    }
}

#[allow(unused_variables)]
impl Serialize for PCSState {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        unimplemented!()
    }
}

#[allow(unused_variables)]
impl AbstractState for PCSState {
    fn is_bottom(&self) -> bool {
        unimplemented!()
    }

    fn join(&mut self, other: &Self) {
        unimplemented!()
    }

    fn widen(&mut self, previous: &Self) {
        unimplemented!()
    }
}
