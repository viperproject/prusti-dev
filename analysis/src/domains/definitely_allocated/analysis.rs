// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine},
    domains::DefinitelyAllocatedState,
};
use prusti_rustc_interface::{data_structures::fx::FxHashSet, middle::mir, span::def_id::DefId};

pub struct DefinitelyAllocatedAnalysis<'mir, 'tcx: 'mir> {
    def_id: DefId,
    mir: &'mir mir::Body<'tcx>,
}

impl<'mir, 'tcx: 'mir> DefinitelyAllocatedAnalysis<'mir, 'tcx> {
    pub fn new(def_id: DefId, mir: &'mir mir::Body<'tcx>) -> Self {
        DefinitelyAllocatedAnalysis { def_id, mir }
    }
}

impl<'mir, 'tcx: 'mir> FixpointEngine<'mir, 'tcx> for DefinitelyAllocatedAnalysis<'mir, 'tcx> {
    type State = DefinitelyAllocatedState<'mir, 'tcx>;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        self.mir
    }

    /// The bottom element of the lattice contains all possible places,
    /// meaning all locals (which includes all their fields)
    fn new_bottom(&self) -> Self::State {
        DefinitelyAllocatedState {
            def_allocated_locals: self.mir.local_decls.indices().collect(),
            mir: self.mir,
        }
    }

    fn new_initial(&self) -> Self::State {
        let mut locals_without_explicit_allocation: FxHashSet<_> =
            self.mir.vars_and_temps_iter().collect();
        for block in self.mir.basic_blocks() {
            for statement in &block.statements {
                match statement.kind {
                    mir::StatementKind::StorageLive(local)
                    | mir::StatementKind::StorageDead(local) => {
                        locals_without_explicit_allocation.remove(&local);
                    }
                    _ => {}
                }
            }
        }
        DefinitelyAllocatedState {
            def_allocated_locals: locals_without_explicit_allocation,
            mir: self.mir,
        }
    }

    fn need_to_widen(_counter: u32) -> bool {
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
