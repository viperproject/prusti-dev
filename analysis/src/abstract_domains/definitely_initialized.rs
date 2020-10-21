// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::AbstractState;
use rustc_middle::mir;

pub struct DefinitelyInitializedState {}

impl<'tcx> AbstractState<'tcx> for DefinitelyInitializedState {
    fn new_bottom() -> Self {
        unimplemented!()
    }

    fn new_initial(args: &[mir::LocalDecl<'tcx>]) -> Self {
        unimplemented!()
    }

    fn widening_threshold() -> u32 {
        unimplemented!()
    }

    fn join(&mut self, other: &Self) {
        unimplemented!()
    }

    fn widen(&mut self, previous: &Self) {
        unimplemented!()
    }

    fn apply_statement_effect(&mut self, location: &mir::Location, stmt: &mir::Statement<'tcx>) {
        unimplemented!()
    }

    fn apply_terminator_effect(&self, location: &mir::Location, terminator: &mir::terminator::Terminator<'tcx>) -> Vec<(mir::BasicBlock, Box<Self>)> {
        unimplemented!()
    }
}
