// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{abstract_interpretation::AbstractState, mir_utils::*, AnalysisError};
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::{mir, ty, ty::TyCtxt};
use rustc_span::def_id::DefId;
use serde::{ser::SerializeSeq, Serialize, Serializer};
use std::{collections::BTreeSet, fmt, mem};

/// A set of MIR places that are definitely initialized at a program point
///
/// Invariant: we never have a place and any of its descendants in the
/// set at the same time. For example, having `x.f` and `x.f.g` in the
/// set at the same time is illegal.
#[derive(Clone)]
pub struct DefinitelyInitializedState<'mir, 'tcx: 'mir> {
    pub(super) def_init_places: FxHashSet<mir::Place<'tcx>>,
    pub(super) def_id: DefId,
    pub(super) mir: &'mir mir::Body<'tcx>,
    pub(super) tcx: TyCtxt<'tcx>,
}

impl<'mir, 'tcx: 'mir> fmt::Debug for DefinitelyInitializedState<'mir, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // ignore tcx & mir
        f.debug_struct("DefinitelyInitializedState")
            .field("def_init_places", &self.def_init_places)
            .finish()
    }
}

impl<'mir, 'tcx: 'mir> PartialEq for DefinitelyInitializedState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        // TODO: This assert is commented out because the stable hasher crashes
        // on MIR that has region ids.
        //
        // debug_assert_eq!(
        //     {
        //         let mut stable_hasher = StableHasher::new();
        //         self.mir.hash_stable(
        //             &mut self.tcx.get_stable_hashing_context(),
        //             &mut stable_hasher,
        //         );
        //         stable_hasher.finish::<Fingerprint>()
        //     },
        //     {
        //         let mut stable_hasher = StableHasher::new();
        //         other.mir.hash_stable(
        //             &mut other.tcx.get_stable_hashing_context(),
        //             &mut stable_hasher,
        //         );
        //         stable_hasher.finish::<Fingerprint>()
        //     },
        // );
        self.def_init_places == other.def_init_places
    }
}

impl<'mir, 'tcx: 'mir> Eq for DefinitelyInitializedState<'mir, 'tcx> {}

impl<'mir, 'tcx: 'mir> Serialize for DefinitelyInitializedState<'mir, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut seq = serializer.serialize_seq(Some(self.def_init_places.len()))?;
        let ordered_place_set: BTreeSet<_> = self.def_init_places.iter().collect();
        for place in ordered_place_set {
            seq.serialize_element(&format!("{:?}", place))?;
        }
        seq.end()
    }
}

impl<'mir, 'tcx: 'mir> DefinitelyInitializedState<'mir, 'tcx> {
    pub fn get_def_init_places(&self) -> &FxHashSet<mir::Place<'tcx>> {
        &self.def_init_places
    }

    /// The top element of the lattice contains no places
    pub fn new_top(def_id: DefId, mir: &'mir mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        Self {
            def_init_places: FxHashSet::default(),
            def_id,
            mir,
            tcx,
        }
    }

    pub fn is_top(&self) -> bool {
        self.def_init_places.is_empty()
    }

    pub fn check_invariant(&self) {
        for &place1 in self.def_init_places.iter() {
            for &place2 in self.def_init_places.iter() {
                if place1 != place2 {
                    debug_assert!(
                        !is_prefix(place1, place2),
                        "The place {:?} is a prefix of the place {:?}",
                        place2,
                        place1
                    );
                    debug_assert!(
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
    fn set_place_initialised(&mut self, place: mir::Place<'tcx>) {
        if cfg!(debug_assertions) {
            self.check_invariant();
        }

        // First, check that the place is not already marked as
        // definitely initialized.
        if !self
            .def_init_places
            .iter()
            .any(|&current| is_prefix(place, current))
        {
            // To maintain the invariant that we do not have a place and its
            // prefix in the set, we remove all places for which the given
            // one is a prefix.
            self.def_init_places
                .retain(|&current| !is_prefix(current, place));
            self.def_init_places.insert(place);
            // If all fields of a struct are definitely initialized,
            // just keep info that the struct is definitely initialized.
            collapse(self.mir, self.tcx, &mut self.def_init_places, place);
        }

        if cfg!(debug_assertions) {
            self.check_invariant();
        }
    }

    /// Sets `place` as (possibly) uninitialised (see place_set/remove())
    fn set_place_uninitialised(&mut self, place: mir::Place<'tcx>) {
        if cfg!(debug_assertions) {
            self.check_invariant();
        }

        let old_places = mem::take(&mut self.def_init_places);
        for old_place in old_places {
            if is_prefix(place, old_place) {
                // We are uninitializing a field of the place `old_place`.
                self.def_init_places
                    .extend(expand(self.mir, self.tcx, old_place, place));
            } else if is_prefix(old_place, place) {
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
        for &place1 in self.def_init_places.iter() {
            debug_assert!(
                !is_prefix(place1, place) && !is_prefix(place, place1),
                "Bug: failed to ensure that there are no prefixes: place={:?} place1={:?}",
                place,
                place1
            );
        }

        if cfg!(debug_assertions) {
            self.check_invariant();
        }
    }

    /// If the operand is move, make the place uninitialised
    /// If the place is a Copy type, uninitialise the place iif `move_out_copy_types` is true.
    fn apply_operand_effect(&mut self, operand: &mir::Operand<'tcx>, move_out_copy_types: bool) {
        if let mir::Operand::Move(place) = operand {
            let mut uninitialise = true;
            if !move_out_copy_types {
                let ty = place.ty(&self.mir.local_decls, self.tcx).ty;
                let param_env = self.tcx.param_env(self.def_id);
                uninitialise = !is_copy(self.tcx, ty, param_env);
            }
            if uninitialise {
                self.set_place_uninitialised(*place);
            }
        }
    }

    /// If the place is a Copy type, uninitialise the place iif `move_out_copy_types` is true.
    pub(super) fn apply_statement_effect(
        &mut self,
        location: mir::Location,
        move_out_copy_types: bool,
    ) -> Result<(), AnalysisError> {
        let statement = &self.mir[location.block].statements[location.statement_index];
        match statement.kind {
            mir::StatementKind::Assign(box (target, ref source)) => {
                match source {
                    mir::Rvalue::Repeat(ref operand, _)
                    | mir::Rvalue::Cast(_, ref operand, _)
                    | mir::Rvalue::UnaryOp(_, ref operand)
                    | mir::Rvalue::Use(ref operand) => {
                        self.apply_operand_effect(operand, move_out_copy_types);
                    }
                    mir::Rvalue::BinaryOp(_, box (ref operand1, ref operand2))
                    | mir::Rvalue::CheckedBinaryOp(_, box (ref operand1, ref operand2)) => {
                        self.apply_operand_effect(operand1, move_out_copy_types);
                        self.apply_operand_effect(operand2, move_out_copy_types);
                    }
                    mir::Rvalue::Aggregate(_, ref operands) => {
                        for operand in operands.iter() {
                            self.apply_operand_effect(operand, move_out_copy_types);
                        }
                    }
                    _ => {}
                }

                self.set_place_initialised(target);
            }
            mir::StatementKind::StorageDead(local) => {
                let place = mir::Place {
                    local,
                    projection: ty::List::empty(),
                };
                self.set_place_uninitialised(place);
            }
            _ => {}
        }

        Ok(())
    }

    /// If the place is a Copy type, uninitialise the place iif `move_out_copy_types` is true.
    pub(super) fn apply_terminator_effect(
        &self,
        location: mir::Location,
        move_out_copy_types: bool,
    ) -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        let mut new_state = self.clone();
        let mut res_vec = Vec::new();
        let terminator = self.mir[location.block].terminator();
        match terminator.kind {
            mir::TerminatorKind::SwitchInt { ref discr, .. } => {
                // only operand has an effect on definitely initialized places, all successors
                // get the same state
                new_state.apply_operand_effect(discr, move_out_copy_types);

                for &bb in terminator.successors() {
                    res_vec.push((bb, new_state.clone()));
                }
            }
            mir::TerminatorKind::Drop {
                place,
                target,
                unwind,
            } => {
                new_state.set_place_uninitialised(place);
                res_vec.push((target, new_state));

                if let Some(bb) = unwind {
                    // imprecision for error states
                    res_vec.push((bb, Self::new_top(self.def_id, self.mir, self.tcx)));
                }
            }
            mir::TerminatorKind::DropAndReplace {
                place,
                ref value,
                target,
                unwind,
            } => {
                new_state.set_place_uninitialised(place);
                new_state.apply_operand_effect(value, move_out_copy_types);
                new_state.set_place_initialised(place);
                res_vec.push((target, new_state));

                if let Some(bb) = unwind {
                    // imprecision for error states
                    res_vec.push((bb, Self::new_top(self.def_id, self.mir, self.tcx)));
                }
            }
            mir::TerminatorKind::Call {
                ref func,
                ref args,
                destination,
                cleanup,
                ..
            } => {
                for arg in args.iter() {
                    new_state.apply_operand_effect(arg, move_out_copy_types);
                }
                new_state.apply_operand_effect(func, move_out_copy_types);
                if let Some((place, bb)) = destination {
                    new_state.set_place_initialised(place);
                    res_vec.push((bb, new_state));
                }

                if let Some(bb) = cleanup {
                    // imprecision for error states
                    res_vec.push((bb, Self::new_top(self.def_id, self.mir, self.tcx)));
                }
            }
            mir::TerminatorKind::Assert {
                ref cond,
                target,
                cleanup,
                ..
            } => {
                new_state.apply_operand_effect(cond, move_out_copy_types);
                res_vec.push((target, new_state));

                if let Some(bb) = cleanup {
                    // imprecision for error states
                    res_vec.push((bb, Self::new_top(self.def_id, self.mir, self.tcx)));
                }
            }
            mir::TerminatorKind::Yield {
                ref value,
                resume,
                drop,
                ..
            } => {
                // TODO: resume_arg?
                new_state.apply_operand_effect(value, move_out_copy_types);
                res_vec.push((resume, new_state));

                if let Some(bb) = drop {
                    // imprecision for error states
                    res_vec.push((bb, Self::new_top(self.def_id, self.mir, self.tcx)));
                }
            }
            mir::TerminatorKind::InlineAsm { .. } => {
                return Err(AnalysisError::UnsupportedStatement(location))
            }

            _ => {
                for &bb in terminator.successors() {
                    // no operation -> no change of state
                    res_vec.push((bb, self.clone()));
                }
            }
        }

        Ok(res_vec)
    }
}

impl<'mir, 'tcx: 'mir> AbstractState for DefinitelyInitializedState<'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        if self.def_init_places.len() == self.mir.local_decls.len() {
            self.mir
                .local_decls
                .indices()
                .all(|local| self.def_init_places.contains(&local.into()))
        } else {
            false
        }
    }

    /// The lattice join intersects the two place sets
    fn join(&mut self, other: &Self) {
        if cfg!(debug_assertions) {
            self.check_invariant();
            other.check_invariant();
        }

        let mut intersection = FxHashSet::default();
        // TODO: make more efficient/modify self directly?
        let mut propagate_places_fn =
            |place_set1: &FxHashSet<mir::Place<'tcx>>, place_set2: &FxHashSet<mir::Place<'tcx>>| {
                for &place in place_set1.iter() {
                    // find matching place in place_set2:
                    // if there is a matching place that contains exactly the same or more memory
                    // locations, place can be added to the resulting intersection
                    for &potential_prefix in place_set2.iter() {
                        if is_prefix(place, potential_prefix) {
                            intersection.insert(place);
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

        if cfg!(debug_assertions) {
            self.check_invariant();
        }
    }

    fn widen(&mut self, _previous: &Self) {
        unimplemented!()
    }
}
