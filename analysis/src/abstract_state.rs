// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::mir;
use std::vec::Vec;


pub trait AbstractState<'tcx> {
    //fn make_top(self) -> Self;
    //fn make_bottom(self) -> Self;
    fn new_bottom() -> Self;
    //fn new_top() -> Self;
    fn new_initial(args: &[mir::LocalDecl<'tcx>]) -> Self;

    fn widening_threshold() -> u32;

    //fn is_top(&self) -> bool;
    //fn is_bottom(&self) -> bool;
    //fn less_equal(&self, other: &Self) -> bool;
    fn join(&mut self, other: &Self);
    //fn meet(&mut self, other: &Self) -> Self;
    fn widen(&mut self, previous: &Self);

    fn apply_statement_effect(&mut self, location: &mir::Location, stmt: &mir::Statement<'tcx>);
    fn apply_terminator_effect(&self, location: &mir::Location, terminator: &mir::terminator::Terminator<'tcx>) -> Vec<(mir::BasicBlock, Box<Self>)>;
}
