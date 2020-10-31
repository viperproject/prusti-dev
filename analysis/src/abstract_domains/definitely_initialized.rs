// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{AbstractState, AnalysisError};
use crate::abstract_domains::place_utils::*;
use rustc_middle::mir;
use std::collections::HashSet;
use rustc_middle::ty::TyCtxt;
use std::mem;


/// A set of MIR places that are definitely initialized at a program point
///
/// Invariant: we never have a place and any of its descendants in the
/// set at the same time. For example, having `x.f` and `x.f.g` in the
/// set at the same time is illegal.
pub struct DefinitelyInitializedState<'tcx> {
    def_init_places: HashSet<mir::Place<'tcx>>,
    //mir: &'a mir::Body<'tcx>, TODO: store mir instead of giving it to apply_statement/terminator_effect?
    tcx: TyCtxt<'tcx>,
}



impl<'tcx>  DefinitelyInitializedState<'tcx>  {
    pub fn check_invariant(&self) {
        for place1 in self.def_init_places.iter() {
            for place2 in self.def_init_places.iter() {
                if place1 != place2 {
                    assert!(
                        !is_prefix(place1, place2),
                        "The place {:?} is a prefix of the place {:?}",
                        place2,
                        place1
                    );
                    assert!(
                        !is_prefix(place2, place1),
                        "The place {:?} is a prefix of the place {:?}",
                        place1,
                        place2
                    );
                }
            }
        }
    }

    /// Sets `place` as definitely initialized (see place_set/insert()
    fn set_place_initialised(&mut self, place: &mir::Place<'tcx>, mir: &mir::Body<'tcx>) {
        self.check_invariant();

        // First, check that the place is not already marked as
        // definitely initialized.
        if !self.def_init_places.iter().any(|current| is_prefix(place, current)) {
            // To maintain the invariant that we do not have a place and its
            // prefix in the set, we remove all places for which the given
            // one is a prefix.
            self.def_init_places.retain(|current| !is_prefix(current, place));
            self.def_init_places.insert(place.clone());
            // If all fields of a struct are definitely initialized,
            // just keep info that the struct is definitely initialized.
            collapse(mir, self.tcx, &mut self.def_init_places, place);
        }
        self.check_invariant();
    }

    /// Sets `place` as (possibly) uninitialized (see place_set/remove())
    fn set_place_uninitialised(&mut self, place: &mir::Place<'tcx>, mir: &mir::Body<'tcx>) {
        self.check_invariant();

        let old_places = mem::replace(&mut self.def_init_places, HashSet::new());
        for old_place in old_places {
            if is_prefix(place, &old_place) {
                // We are uninitializing a field of the place `old_place`.
                self.def_init_places.extend(expand(mir, self.tcx, &old_place, place));
            } else if is_prefix(&old_place, place) {
                // We are uninitializing a place of which only some
                // fields are initialized. Just remove all initialized
                // fields.
                // This happens when the target place is already
                // initialized.
            } else {
                self.def_init_places.insert(old_place);
            }
        }

        // Check that place is properly removed
        for place1 in self.def_init_places.iter() {
            assert!(
                !is_prefix(place1, place) && !is_prefix(place, place1),
                "Bug: failed to ensure that there are no prefixes: place={:?} place1={:?}",
                place,
                place1
            );
        }

        self.check_invariant();
    }

    /// If the operand is move, make the place uninitialized
    fn apply_operand_effect(&mut self, operand: &mir::Operand<'tcx>, mir: &mir::Body<'tcx>) {
        if let mir::Operand::Move(place) = operand {
            self.set_place_uninitialised(place, mir);
        }
    }
}

impl<'tcx> AbstractState<'tcx> for DefinitelyInitializedState<'tcx>
    where Self: Clone {

    /// contains all possible places = all locals  //TODO: correct: only locals?
    fn new_bottom(mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let mut places = HashSet::new();
        for local in mir.local_decls.indices().skip(1) {        // skip return value pointer
            places.insert(local.clone().into());
        }
        Self {def_init_places: places, tcx}
    }

    fn new_initial(mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        // Top = empty set
        let mut places = HashSet::new();
        // join/insert places in arguments
        // they are guaranteed to be disjoint and not prefixes of each other,
        // therefore insert them directly
        for local in mir.args_iter() {
            places.insert(local.clone().into());
        }
        Self {def_init_places: places, tcx}
    }

    fn need_to_widen(counter: &u32) -> bool {
        false   //TODO: check
    }

    /// = intersection of place sets
    fn join(&mut self, other: &Self) {
        self.check_invariant();
        other.check_invariant();

        let mut intersection = HashSet::new();
        // TODO: make more efficient/modify self directly?
        let mut propagate_places_fn = |place_set1: &HashSet<mir::Place<'tcx>>, place_set2: &HashSet<mir::Place<'tcx>>| {
            for place in place_set1.iter() {
                // find matching place in place_set2:
                // if there is a matching place that contains exactly the same or more memory locations,
                // place can be added to the resulting intersection
                for potential_prefix in place_set2.iter() {
                    if is_prefix(place, potential_prefix) {
                        intersection.insert(place.clone());
                        break;
                    }
                }
            }
        };

        let self_places = &self.def_init_places;
        let other_places = &other.def_init_places;
        propagate_places_fn(self_places, other_places);
        propagate_places_fn(other_places, self_places);
        self.def_init_places = intersection;
        self.check_invariant();
    }

    fn widen(&mut self, previous: &Self) {
        unimplemented!()
    }

    fn apply_statement_effect(&mut self, location: &mir::Location, mir: &mir::Body<'tcx>)-> Result<(), AnalysisError> {
        let statement = &mir[location.block].statements[location.statement_index];
        match statement.kind {
            mir::StatementKind::Assign(box (ref target, ref source)) => {
                match source {
                    mir::Rvalue::Repeat(ref operand, _)
                    | mir::Rvalue::Cast(_, ref operand, _)
                    | mir::Rvalue::UnaryOp(_, ref operand)
                    | mir::Rvalue::Use(ref operand) => {
                        self.apply_operand_effect(operand, mir);
                    }
                    mir::Rvalue::BinaryOp(_, ref operand1, ref operand2)
                    | mir::Rvalue::CheckedBinaryOp(_, ref operand1, ref operand2) => {
                        self.apply_operand_effect(operand1, mir);
                        self.apply_operand_effect(operand2, mir);
                    }
                    mir::Rvalue::Aggregate(_, ref operands) => {
                        for operand in operands.iter() {
                            self.apply_operand_effect(operand, mir);
                        }
                    }
                    _ => {}
                }

                self.set_place_initialised(target, mir);
            }
            _ => {}
        }

        Ok(())
    }

    fn apply_terminator_effect(&self, location: &mir::Location, mir: &mir::Body<'tcx>)
        -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {

        let mut new_state = self.clone();
        let mut res_vec = Vec::new();
        let terminator = mir[location.block].terminator();
        match terminator.kind {
            mir::TerminatorKind::SwitchInt { ref discr, .. } => {
                // only operand has an effect on definitely intialized places, all successors get the same state
                new_state.apply_operand_effect(discr, mir);

                for bb in terminator.successors() {
                    res_vec.push((*bb, new_state.clone()));
                }
            }
            mir::TerminatorKind::Drop { ref place, target, unwind } => {
                new_state.set_place_uninitialised(place, mir);
                if let Some(bb) = unwind {
                    res_vec.push((bb, new_state.clone()));       // TODO: correct? still uninit?
                }
                res_vec.push((target, new_state));
            }
            mir::TerminatorKind::DropAndReplace { ref place, ref value, target, unwind } => {
                //TODO: setting uninit necessary?
                new_state.set_place_uninitialised(place, mir);
                new_state.apply_operand_effect(value, mir);
                new_state.set_place_initialised(place, mir);
                if let Some(bb) = unwind {
                    res_vec.push((bb, new_state.clone()));
                }
                res_vec.push((target, new_state));
            }
            mir::TerminatorKind::Call { ref func, ref args, ref destination, cleanup, .. } => {
                new_state.apply_operand_effect(func, mir);
                for arg in args.iter() {
                    new_state.apply_operand_effect(arg, mir);
                }
                if let Some(bb) = cleanup {
                    //TODO: correct? assignment failed? what else?
                    res_vec.push((bb, new_state.clone()));
                }
                if let Some((place, bb)) = destination {
                    new_state.set_place_initialised(place, mir);
                    res_vec.push((*bb, new_state));
                }
            }
            mir::TerminatorKind::Assert { ref cond, target, cleanup, .. } => {
                if let Some(bb) = cleanup {
                    //TODO: correct? operand failed?
                    res_vec.push((bb, new_state.clone()));
                }
                new_state.apply_operand_effect(cond, mir);
                res_vec.push((target, new_state));
            }
            mir::TerminatorKind::Yield { ref value, resume, drop, .. } => { //TODO: resume_arg
                if let Some(bb) = drop {
                    //TODO: correct? operand not executed?
                    res_vec.push((bb, new_state.clone()));
                }
                new_state.apply_operand_effect(value, mir);
                res_vec.push((resume, new_state));
            }
            _ => {return Err(AnalysisError::UnsupportedStatement(*location))}
        }

        Ok(res_vec)
    }
}
