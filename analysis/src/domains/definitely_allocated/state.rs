// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{abstract_interpretation::AbstractState, AnalysisError};
use prusti_rustc_interface::{data_structures::fx::FxHashSet, middle::mir};
use serde::{ser::SerializeSeq, Serialize, Serializer};
use std::{collections::BTreeSet, fmt};

/// A set of MIR locals that are definitely allocated at a program point
#[derive(Clone)]
pub struct DefinitelyAllocatedState<'mir, 'tcx: 'mir> {
    pub(super) def_allocated_locals: FxHashSet<mir::Local>,
    pub(super) mir: &'mir mir::Body<'tcx>,
}

impl<'mir, 'tcx: 'mir> fmt::Debug for DefinitelyAllocatedState<'mir, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // ignore mir
        f.debug_struct("DefinitelyAllocatedState")
            .field("def_allocated_locals", &self.def_allocated_locals)
            .finish()
    }
}

impl<'mir, 'tcx: 'mir> PartialEq for DefinitelyAllocatedState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.def_allocated_locals == other.def_allocated_locals
    }
}

impl<'mir, 'tcx: 'mir> Eq for DefinitelyAllocatedState<'mir, 'tcx> {}

impl<'mir, 'tcx: 'mir> Serialize for DefinitelyAllocatedState<'mir, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_seq(Some(self.def_allocated_locals.len()))?;
        let oredered_set: BTreeSet<_> = self.def_allocated_locals.iter().collect();
        for local in oredered_set {
            seq.serialize_element(&format!("{:?}", local))?;
        }
        seq.end()
    }
}

impl<'mir, 'tcx: 'mir> DefinitelyAllocatedState<'mir, 'tcx> {
    pub fn get_def_allocated_locals(&self) -> &FxHashSet<mir::Local> {
        &self.def_allocated_locals
    }

    /// The top element of the lattice contains no locals
    pub fn new_top(mir: &'mir mir::Body<'tcx>) -> Self {
        Self {
            def_allocated_locals: FxHashSet::default(),
            mir,
        }
    }

    pub fn is_top(&self) -> bool {
        self.def_allocated_locals.is_empty()
    }

    /// Sets `local` as allocated.
    fn set_local_allocated(&mut self, local: mir::Local) {
        self.def_allocated_locals.insert(local);
    }

    /// Sets `local` as (possibly) not allocated.
    fn set_place_unallocated(&mut self, local: mir::Local) {
        self.def_allocated_locals.remove(&local);
    }

    pub(super) fn apply_statement_effect(
        &mut self,
        location: mir::Location,
    ) -> Result<(), AnalysisError> {
        let statement = &self.mir[location.block].statements[location.statement_index];
        match statement.kind {
            mir::StatementKind::StorageLive(local) => {
                self.set_local_allocated(local);
            }
            mir::StatementKind::StorageDead(local) => {
                self.set_place_unallocated(local);
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn apply_terminator_effect(
        &self,
        location: mir::Location,
    ) -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        let mut res_vec = Vec::new();
        let terminator = self.mir[location.block].terminator();
        for bb in terminator.successors() {
            res_vec.push((bb, self.clone()));
        }
        Ok(res_vec)
    }
}

impl<'mir, 'tcx: 'mir> AbstractState for DefinitelyAllocatedState<'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        self.def_allocated_locals.len() == self.mir.local_decls.len()
    }

    /// The lattice join intersects the two sets of locals
    fn join(&mut self, other: &Self) {
        self.def_allocated_locals
            .retain(|local| other.def_allocated_locals.contains(local));
    }

    fn widen(&mut self, _previous: &Self) {
        unimplemented!()
    }
}
