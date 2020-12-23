// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use std::vec::Vec;
use crate::AnalysisError;
use serde::Serialize;


pub trait AbstractState<'a, 'tcx: 'a>: Clone + Eq + Sized + Serialize {   // Sized needed for apply_terminator_effect's return type
    //fn make_top(&mut self) -> Self;
    //fn make_bottom(&mut self) -> Self;
    /// Creates a new abstract state which corresponds to the bottom element in the lattice
    fn new_bottom(mir: &'a mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self;
    /// Checks if the current state corresponds to the bottom element in the lattic
    fn is_bottom(&self) -> bool;
    //fn new_top(mir: &'a mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self;
    //fn is_top(&self) -> bool;
    /// Creates the abstract state at the beginning of the `mir` body
    fn new_initial(mir: &'a mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self;

    //fn less_equal(&self, other: &Self) -> bool;

    /// Determines if the number of times this block was traversed by the analyzer given in `counter`
    /// is large enough to widen the state
    fn need_to_widen(counter: &u32) -> bool;

    /// Lattice operation to join `other` into this state, producing the (least) upper bound
    fn join(&mut self, other: &Self);
    //fn meet(&mut self, other: &Self) -> Self;
    /// Make the state less precise to make the iteration stop by using the difference to the state from the previous iteration given in `previous`
    fn widen(&mut self, previous: &Self);

    /// Change the state according to the statement at `location`
    ///
    /// *The statement can be extracted using `&mir[location.block].statements[location.statement_index]`*
    fn apply_statement_effect(&mut self, location: &mir::Location, mir: &mir::Body<'tcx>)
        -> Result<(), AnalysisError>;

    /// Change the state according to the terminator at `location`
    ///
    /// *The statement can be extracted using `mir[location.block].terminator()`*
    fn apply_terminator_effect(&self, location: &mir::Location, mir: &mir::Body<'tcx>)
        -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError>;
}
