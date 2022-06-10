#![allow(unused_variables)]

// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::abstract_interpretation::{AnalysisResult, FixpointEngine};
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::def_id::DefId;

use super::CondInitializedState;

//  The CondInitAnalysis computes an elaborated version of MaybeInitAnalysis,
//   where each maybe initialized place tracks it's possible initialization sites.
//
//  This information is used in kill elaboration. When a place needs to be killed,
//   we insert a flag (enum, usize) which is updated every time the place is
//   re-initalized.
//
//  PROPERTY: All DefinitelyInitialized places will be CondInitialized.
//
//  PROPERTY: All CondInitialized places with one tag are definitelyInitialized
//
//  PROPERTY: A place is definitely not initialzied exactly when it's not
//   CondInitialzied
//
//
//  Fold/Unfold approximation for kill's:
//
//  1. Partial kills and reassignment:
//  When part of a place is killed, we exchange it into all it's subplaces and give them the same
//  initialization time as their full place. It's as if the entire place was initialized in
//  individual projections each time.
//
// 2. When a full place is killed, we must remove all possible subplaces too (handle open drops)
//
// This approximation is sound for code without borrows.
// The conditional code can be used to conditionally apply wands etc later.
// The approximation is inefficient when we move out a field and then move it back in.

pub struct CondInitializedAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    mir: &'mir mir::Body<'tcx>,
}

impl<'mir, 'tcx: 'mir> CondInitializedAnalysis<'mir, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, mir: &'mir mir::Body<'tcx>) -> Self {
        CondInitializedAnalysis { tcx, def_id, mir }
    }
}

impl<'mir, 'tcx: 'mir> FixpointEngine<'mir, 'tcx> for CondInitializedAnalysis<'mir, 'tcx> {
    type State = CondInitializedState<'mir, 'tcx>;

    fn def_id(&self) -> DefId {
        return self.def_id;
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        return self.mir;
    }

    fn new_bottom(&self) -> Self::State {
        // Identity of union => empty state
        return CondInitializedState::new_bottom(self.def_id(), self.body(), self.tcx);
    }

    fn new_initial(&self) -> Self::State {
        // TODO: This is wrong... I am 100% sure of that.
        //      Add unconditional (read: at bb0) initializations of paramaters here
        return CondInitializedState::new_bottom(self.def_id(), self.body(), self.tcx);
    }

    fn need_to_widen(counter: u32) -> bool {
        return false;
    }

    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()> {
        return state.apply_statement_effect(location);
    }

    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        return state.apply_terminator_effect(location);
    }
}
