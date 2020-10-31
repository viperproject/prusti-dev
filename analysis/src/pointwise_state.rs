// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashMap;
use rustc_middle::mir;
use crate::AbstractState;
use std::marker::PhantomData;

pub struct PointwiseState<'tcx, S: AbstractState<'tcx>> {
    state_before: HashMap<mir::Location, S>,
    /// We use a vector, not a map, to reflect the type of `TerminatorKind::Switch::targets`.
    /// In particular, there might be multiple CFG edges all going to the same CFG block, and we
    /// want to distinguish them.
    state_after_block: HashMap<mir::BasicBlock, HashMap<mir::BasicBlock, S>>,
    phantom: PhantomData<&'tcx S>,      //for 'tcx
}

impl<'tcx, S: AbstractState<'tcx>> PointwiseState<'tcx, S> {
    pub fn new() -> Self {
        Self {
            state_before: HashMap::new(),
            state_after_block: HashMap::new(),
            phantom: PhantomData::default(),
        }
    }

    /// The location can point to a statement or terminator.
    pub fn lookup_before(&self, location: &mir::Location) -> Option<&S> {
        self.state_before.get(location)
    }

    /// The location should point to a statement, not a terminator.
    pub fn lookup_after(&self, location: &mir::Location) -> Option<&S> {
        self.state_before.get(&location.successor_within_block())
    }

    /// Return the abstract state on the outgoing CFG edges
    pub fn lookup_after_block(&self, block: &mir::BasicBlock) -> Option<&HashMap<mir::BasicBlock, S>> {
        self.state_after_block.get(block)
    }


    /*/// The location can point to a statement or terminator.
    pub(crate) fn lookup_mut_before(&mut self, location: &mir::Location) -> Option<&mut S> {
        unimplemented!();
    }

    /// The location should point to a statement, not a terminator.
    pub(crate) fn lookup_mut_after(&mut self, location: &mir::Location) -> Option<&mut S> {
        unimplemented!();
    }*/

    /// Return the abstract state on the outgoing CFG edges
    pub(crate) fn lookup_mut_after_block(
        &mut self,
        block: &mir::BasicBlock,
    ) -> &mut HashMap<mir::BasicBlock, S> {
        self.state_after_block.entry(*block).or_insert(HashMap::new())
    }

    pub(crate) fn set_before(&mut self, location: &mir::Location, state: S) {
        self.state_before.insert(*location, state);
    }
}
