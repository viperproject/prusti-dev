// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{AbstractState, AnalysisError};
use rustc_middle::mir;

pub struct DefinitelyInitializedState {}

impl AbstractState for DefinitelyInitializedState {
    fn new_bottom() -> Self {
        unimplemented!()
    }

    fn new_initial(args: Vec<&mir::LocalDecl>) -> Self {
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

    fn apply_statement_effect(&mut self, location: &mir::Location, stmt: &mir::Statement)-> Result<(), AnalysisError> {
        unimplemented!()
    }

    fn apply_terminator_effect(&self, location: &mir::Location, terminator: &mir::terminator::Terminator)
        -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        unimplemented!()
    }
}
