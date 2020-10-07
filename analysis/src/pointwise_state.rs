// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{ HashMap, BTreeMap };
use rustc_middle::mir;
use crate::AbstractState;

pub struct PointwiseState<S: AbstractState> {
    state_before: HashMap<mir::Location, S>,
    state_after_block: HashMap<mir::BasicBlock, BTreeMap<mir::BasicBlock, S>>,
}

impl<S: AbstractState> PointwiseState<S> {
    /// The location can point to a statement or terminator.
    pub fn lookup_before(&self, location: mir::Location) -> &S {
        unimplemented!();
    }

    /// The location should point to a statement, not a terminator.
    pub fn lookup_after(&self, location: mir::Location) -> &S {
        unimplemented!();
    }

    /// Return the abstract state on the outgoing CFG edges
    pub fn lookup_afterblock(&self, block: mir::BasicBlock) -> BTreeMap<mir::BasicBlock, &S> {
        unimplemented!();
    }

    /// The location can point to a statement or terminator.
    pub(crate) fn lookup_mut_before(&mut self, location: mir::Location) -> &mut S {
        unimplemented!();
    }

    /// The location should point to a statement, not a terminator.
    pub(crate) fn lookup_mut_after(&mut self, location: mir::Location) -> &mut S {
        unimplemented!();
    }

    /// Return the abstract state on the outgoing CFG edges
    pub(crate) fn lookup_mut_block(
        &mut self,
        block: mir::BasicBlock,
    ) -> BTreeMap<mir::BasicBlock, &mut S> {
        unimplemented!();
    }
}
