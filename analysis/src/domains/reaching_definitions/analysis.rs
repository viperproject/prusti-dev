// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine},
    domains::{DefLocation, ReachingDefsState},
};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, ty::TyCtxt},
    span::def_id::DefId,
};

pub struct ReachingDefsAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    mir: &'mir mir::Body<'tcx>,
}

impl<'mir, 'tcx: 'mir> ReachingDefsAnalysis<'mir, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, mir: &'mir mir::Body<'tcx>) -> Self {
        ReachingDefsAnalysis { tcx, def_id, mir }
    }
}

impl<'mir, 'tcx: 'mir> FixpointEngine<'mir, 'tcx> for ReachingDefsAnalysis<'mir, 'tcx> {
    type State = ReachingDefsState<'mir, 'tcx>;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        self.mir
    }

    /// The bottom element of the lattice contains no definitions,
    /// i.e. all sets of reaching definitions are empty
    ///
    /// For a completely new bottom element we do not even insert any locals with sets into the map.
    fn new_bottom(&self) -> Self::State {
        ReachingDefsState {
            reaching_defs: FxHashMap::default(),
            mir: self.mir,
            tcx: self.tcx,
        }
    }

    fn new_initial(&self) -> Self::State {
        let mut reaching_defs: FxHashMap<mir::Local, FxHashSet<DefLocation>> = FxHashMap::default();
        // insert parameters
        for (idx, local) in self.mir.args_iter().enumerate() {
            let location_set = reaching_defs.entry(local).or_default();
            location_set.insert(DefLocation::Parameter(idx));
        }
        ReachingDefsState {
            reaching_defs,
            mir: self.mir,
            tcx: self.tcx,
        }
    }

    fn need_to_widen(_counter: u32) -> bool {
        // only consider static information (assignments) => no lattice of infinite height
        false
    }

    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()> {
        state.apply_statement_effect(location)
    }

    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        state.apply_terminator_effect(location)
    }
}
