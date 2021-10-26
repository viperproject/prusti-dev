// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine},
    domains::DefinitelyInitializedState,
};
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::def_id::DefId;

pub struct DefinitelyInitializedAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    mir: &'mir mir::Body<'tcx>,
    /// If the place is a Copy type, uninitialise the place iif `move_out_copy_types` is true.
    move_out_copy_types: bool,
}

impl<'mir, 'tcx: 'mir> DefinitelyInitializedAnalysis<'mir, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, mir: &'mir mir::Body<'tcx>) -> Self {
        DefinitelyInitializedAnalysis {
            tcx,
            def_id,
            mir,
            move_out_copy_types: true,
        }
    }

    /// This analysis will not uninitialize Copy types when they are moved.
    pub fn new_relaxed(tcx: TyCtxt<'tcx>, def_id: DefId, mir: &'mir mir::Body<'tcx>) -> Self {
        DefinitelyInitializedAnalysis {
            tcx,
            def_id,
            mir,
            move_out_copy_types: false,
        }
    }
}

impl<'mir, 'tcx: 'mir> FixpointEngine<'mir, 'tcx> for DefinitelyInitializedAnalysis<'mir, 'tcx> {
    type State = DefinitelyInitializedState<'mir, 'tcx>;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        self.mir
    }

    /// The bottom element of the lattice contains all possible places,
    /// meaning all locals (which includes all their fields)
    fn new_bottom(&self) -> Self::State {
        let mut places = FxHashSet::default();
        for local in self.mir.local_decls.indices() {
            places.insert(local.into());
        }
        DefinitelyInitializedState {
            def_init_places: places,
            def_id: self.def_id,
            mir: self.mir,
            tcx: self.tcx,
        }
    }

    fn new_initial(&self) -> Self::State {
        // Top = empty set
        let mut places = FxHashSet::default();
        // join/insert places in arguments
        // they are guaranteed to be disjoint and not prefixes of each other,
        // therefore insert them directly
        for local in self.mir.args_iter() {
            places.insert(local.into());
        }
        DefinitelyInitializedState {
            def_init_places: places,
            def_id: self.def_id,
            mir: self.mir,
            tcx: self.tcx,
        }
    }

    fn need_to_widen(_counter: u32) -> bool {
        false //TODO: check
    }

    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()> {
        state.apply_statement_effect(location, self.move_out_copy_types)
    }

    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        state.apply_terminator_effect(location, self.move_out_copy_types)
    }
}
