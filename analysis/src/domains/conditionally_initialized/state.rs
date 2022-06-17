// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#![allow(dead_code)]
#![allow(unused_variables)]

use crate::{
    abstract_interpretation::AbstractState,
    mir_utils::{self, expand, is_copy, is_prefix},
    AnalysisError, PointwiseState,
};
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::{mir, mir::Location, ty::TyCtxt};
use rustc_span::def_id::DefId;
use serde::{Serialize, Serializer};
use std::iter::once;

use rustc_data_structures::stable_map::FxHashMap;
use rustc_middle::mir::{BasicBlock, Place};

// TODO:
//
// Currently, we're using FixpointEngine which only operated on MIR.
// We want this to operate on MIR mircocode.
//
// What we have right now duplicates concerns in that it's both guessing
// kill locations/micro effects from the MIR, and inferring their
// meaning.
//
// This will probably involve rewriting the fixpoint engine, which allows
// for a chance to do a more efficient GenKill analysis instead of the
// current iterative method (this is essentially a GenKill problem afaik)

#[derive(Clone)]
pub struct PlaceBBMap<'tcx> {
    pub map: FxHashMap<mir_utils::Place<'tcx>, FxHashSet<BasicBlock>>,
}

impl<'tcx> PlaceBBMap<'tcx> {
    pub fn coherent_insert(&mut self, p: mir_utils::Place<'tcx>, bb: BasicBlock) {
        if let Some(self_p_bbs) = self.map.get_mut(&p.into()) {
            // TODO: If we insert at a point where we already have a conflicting place, what happens?
            self_p_bbs.extend(once(bb));
        } else {
            let mut new_bbs: FxHashSet<BasicBlock> = FxHashSet::default();
            new_bbs.extend(once(bb));
            self.map.insert(p.clone().into(), new_bbs);
        }
    }
}

impl<'tcx> Default for PlaceBBMap<'tcx> {
    fn default() -> Self {
        Self {
            map: Default::default(),
        }
    }
}

#[derive(Clone)]
pub struct CondInitializedState<'mir, 'tcx: 'mir> {
    pub(super) set: Option<PlaceBBMap<'tcx>>,
    pub(super) def_id: DefId,
    pub(super) mir: &'mir mir::Body<'tcx>,
    pub(super) tcx: TyCtxt<'tcx>,
}

impl<'mir, 'tcx: 'mir> PartialEq for CondInitializedState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        todo!();
    }
}

impl<'mir, 'tcx: 'mir> Eq for CondInitializedState<'mir, 'tcx> {}

impl<'mir, 'tcx: 'mir> Serialize for CondInitializedState<'mir, 'tcx> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        todo!()
    }
}

impl<'mir, 'tcx: 'mir> CondInitializedState<'mir, 'tcx> {
    pub fn new_bottom(
        def_id: DefId,
        mir: &'mir mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> CondInitializedState<'mir, 'tcx> {
        return CondInitializedState {
            set: Some(PlaceBBMap::default()),
            def_id,
            mir,
            tcx,
        };
    }

    pub fn new_top(
        def_id: DefId,
        mir: &'mir mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> CondInitializedState<'mir, 'tcx> {
        return CondInitializedState {
            set: None,
            def_id,
            mir,
            tcx,
        };
    }

    /// Kill all references to a place
    /// Also kill all places which are subplaces of the killed place
    // TODO: Pretty sure this implementation is super bad... it copies everything every time.
    // Fix this if we end up using this analysis
    pub fn coherent_kill(
        &mut self,
        p: mir_utils::Place<'tcx>,
        location: Location,
    ) -> Result<(), ()> {
        if let Some(set) = &mut self.set {
            // Places to add
            let mut new_places: Vec<mir_utils::Place<'tcx>> = vec![];
            // Places to delete
            let mut remove_places: Vec<mir_utils::Place<'tcx>> = vec![];
            for (set_place, set_bbs) in set.map.iter_mut() {
                if is_prefix(p, *set_place) {
                    // p is a prefix of a place in the set. Expand until we can delete the place,
                    // then delete it (by not adding it). Delete the uppermost place.
                    remove_places.push(set_place.clone());
                    new_places.extend(expand(self.mir, self.tcx, set_place.clone(), p.clone()));
                } else if is_prefix(*set_place, p) {
                    // Open drop. Delete the place.
                    remove_places.push(set_place.clone());
                } else {
                    // Unrelated, no need to do anything
                }
            }
            for place in remove_places.iter() {
                set.map.remove(place);
            }

            // Newly expanded places are tagged with their expansion location
            let mut new_bbs: FxHashSet<BasicBlock> = FxHashSet::default();
            new_bbs.extend(once(location.block));
            for place in new_places.iter() {
                set.map.insert(*place, new_bbs.clone());
            }

            return Ok(());
        } else {
            // Top expansion not supported in this representation... yet. TODO.
            return Err(());
        }
    }

    /// Insert other into self
    pub fn coherent_insert(&mut self, p: mir_utils::Place<'tcx>, location: Location) {
        if let Some(s) = &mut self.set {
            s.coherent_insert(p, location.block);
        }
        // By idempotency of top, Top insert anything else is unchanged
    }

    pub fn coherent_union(&mut self, other: &CondInitializedState<'mir, 'tcx>) {
        if let Some(s) = &mut self.set {
            if let Some(os) = &other.set {
                for (p, bb) in os.map.iter() {
                    if let Some(self_p_bbs) = s.map.get_mut(p) {
                        self_p_bbs.extend(bb);
                    } else {
                        s.map.insert(p.clone(), bb.clone());
                    }
                }
            } else {
                // By idempotency
                self.set = None;
            }
        } else {
            // Top is join-idempotent
        }
    }

    // Kill operands that are not copy
    fn apply_operand_effect(&mut self, operand: &mir::Operand<'tcx>, location: mir::Location) {
        if let mir::Operand::Move(place) = operand {
            let ty = place.ty(&self.mir.local_decls, self.tcx).ty;
            let param_env = self.tcx.param_env(self.def_id);
            if !is_copy(self.tcx, ty, param_env) {
                let _ = self.coherent_kill((*place).into(), location);
            }
        }
    }

    pub(super) fn apply_statement_effect(
        &mut self,
        location: mir::Location,
    ) -> Result<(), AnalysisError> {
        let statement = &self.mir[location.block].statements[location.statement_index];
        match statement.kind {
            mir::StatementKind::Assign(box (target, ref source)) => {
                match source {
                    mir::Rvalue::Repeat(ref operand, _)
                    | mir::Rvalue::Cast(_, ref operand, _)
                    | mir::Rvalue::UnaryOp(_, ref operand)
                    | mir::Rvalue::Use(ref operand) => {
                        self.apply_operand_effect(operand, location);
                    }
                    mir::Rvalue::BinaryOp(_, box (ref operand1, ref operand2))
                    | mir::Rvalue::CheckedBinaryOp(_, box (ref operand1, ref operand2)) => {
                        self.apply_operand_effect(operand1, location);
                        self.apply_operand_effect(operand2, location);
                    }
                    mir::Rvalue::Aggregate(_, ref operands) => {
                        for operand in operands.iter() {
                            self.apply_operand_effect(operand, location);
                        }
                    }
                    _ => {}
                }
                let _ = self.coherent_kill(target.into(), location);
                self.coherent_insert(target.into(), location);
            }
            mir::StatementKind::StorageDead(local) => {
                // https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/struct.Place.html
                // Each local naturally corresponds to the place Place { local, projection: [] }.
                // This place has the address of the local’s allocation and the type of the local.
                let _ = self.coherent_kill(
                    Place {
                        local,
                        projection: rustc_middle::ty::List::empty(),
                    }
                    .into(),
                    location,
                );
            }
            _ => {}
        }

        return Ok(());
    }

    pub(super) fn apply_terminator_effect(
        &self,
        location: mir::Location,
    ) -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        let mut new_state = self.clone();
        let mut res_vec = Vec::new();
        let terminator = self.mir[location.block].terminator();
        match terminator.kind {
            mir::TerminatorKind::SwitchInt { ref discr, .. } => {
                // only operand has an effect on definitely initialized places, all successors
                // get the same state
                new_state.apply_operand_effect(discr, location);

                for &bb in terminator.successors() {
                    res_vec.push((bb, new_state.clone()));
                }
            }
            mir::TerminatorKind::Drop {
                place,
                target,
                unwind,
            } => {
                let _ = new_state.coherent_kill(place.into(), location);
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
                let _ = new_state.coherent_kill(place.into(), location);
                new_state.apply_operand_effect(value, location);
                new_state.coherent_insert(place.into(), location);
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
                    new_state.apply_operand_effect(arg, location);
                }
                new_state.apply_operand_effect(func, location);
                if let Some((place, bb)) = destination {
                    new_state.coherent_insert(place.into(), location);
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
                new_state.apply_operand_effect(cond, location);
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
                new_state.apply_operand_effect(value, location);
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

    pub fn pprint_state(&self) {
        if let Some(s) = &self.set {
            for (p, bbs) in s.map.iter() {
                print!("\t\t{:#?}: ", p);
                for b in bbs.iter() {
                    print!("{:#?} ", b);
                }
                println!();
            }
        } else {
            println!("\t\tT");
        }
    }
}

impl<'mir, 'tcx: 'mir> PointwiseState<'mir, 'tcx, CondInitializedState<'mir, 'tcx>> {
    pub fn pprint_trace(&self) {
        for (bbno, bbdata) in self.mir.basic_blocks().iter_enumerated() {
            println!();
            println!("==================== {:#?} ==================== ", bbno);
            let mut stmt_idx: usize = 0;
            for stmt in bbdata.statements.iter() {
                if let Some(st_before) = self.lookup_before(Location {
                    block: bbno,
                    statement_index: stmt_idx,
                }) {
                    st_before.pprint_state();
                } else {
                    println!("No before state.");
                }

                println!("\t{:#?}", stmt);

                if let Some(st_after) = self.lookup_after(Location {
                    block: bbno,
                    statement_index: stmt_idx,
                }) {
                    st_after.pprint_state();
                } else {
                    println!("No after state.");
                }

                println!();
                stmt_idx += 1;
            }

            if let Some(t) = &bbdata.terminator {
                println!("\t{:#?}", t.kind);
            }

            if let Some(ns) = self.lookup_after_block(bbno) {
                for (b, st) in ns.iter() {
                    println!("\t- if terminates to {:#?}:", b);
                    st.pprint_state();
                }
            } else {
                println!("No outgoing edges");
            }
        }
    }
}

impl<'mir, 'tcx: 'mir> AbstractState for CondInitializedState<'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        // Identity for join is no states
        if let Some(s) = &self.set {
            return s.map.is_empty();
        } else {
            return false;
        }
    }

    fn join(&mut self, other: &Self) {
        self.coherent_union(other);
    }

    fn widen(&mut self, previous: &Self) {
        todo!()
    }
}

/*
    pub fn get_def_init_mir_places(&self) -> FxHashSet<mir::Place<'tcx>> {
        self.def_init_places.iter().map(|place| **place).collect()
    }

    pub fn is_top(&self) -> bool {
        self.def_init_places.is_empty()
    }

    /// Sets `place` as definitely initialized (see place_set/insert()
    fn set_place_initialised(&mut self, place: mir::Place<'tcx>) {
        let place = place.into();
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
        let place = place.into();
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


*/

/*
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
            |place_set1: &FxHashSet<Place<'tcx>>, place_set2: &FxHashSet<Place<'tcx>>| {
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
 */
