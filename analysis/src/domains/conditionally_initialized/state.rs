#![allow(dead_code)]
#![allow(unused_variables)]
// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::AbstractState, mir_utils::is_copy, AnalysisError, PointwiseState,
};
use rustc_data_structures::fx::FxHashSet;
use rustc_middle::{mir, mir::Location, ty::TyCtxt};
use rustc_span::def_id::DefId;
use serde::{Serialize, Serializer};
use std::iter::once;

use rustc_data_structures::stable_map::FxHashMap;
use rustc_middle::mir::{BasicBlock, Place};

// use super::CondInitializedAnalysis;

/// A set of possibly intialized MIR places annotated with the basic block
/// they might have been initialized at
///
/// Invariant: we never have a place and any of its descendants in the
/// set at the same time. For example, having `x.f` and `x.f.g` in the
/// set at the same time is illegal.

// When set is None, we interpret it as Top
//  (otherwise, the top element would be |every place| * |every bb| which is huge.
//   top is idempotent for join as is None to Option's monadic composition.
//  )

#[derive(Clone)]
pub struct CondInitializedState<'mir, 'tcx: 'mir> {
    pub(super) set: Option<FxHashMap<Place<'tcx>, FxHashSet<BasicBlock>>>,
    pub(super) def_id: DefId,
    pub(super) mir: &'mir mir::Body<'tcx>,
    pub(super) tcx: TyCtxt<'tcx>,
}

/*
impl<'mir, 'tcx: 'mir> fmt::Debug for DefinitelyInitializedState<'mir, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // ignore tcx & mir
        f.debug_struct("DefinitelyInitializedState")
            .field("def_init_places", &self.def_init_places)
            .finish()
    }
}
*/

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

/*

impl<'mir, 'tcx: 'mir> PartialEq for CondInitializedState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
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

*/

impl<'mir, 'tcx: 'mir> CondInitializedState<'mir, 'tcx> {
    pub fn new_bottom(
        def_id: DefId,
        mir: &'mir mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> CondInitializedState<'mir, 'tcx> {
        return CondInitializedState {
            set: Some(FxHashMap::default()),
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
    pub fn coherent_kill(&mut self, p: Place<'tcx>) {
        if let Some(s) = &mut self.set {
            s.remove_entry(&p);
        } else {
            todo!("Internal error: expansion of Top value. ");
        }
    }

    /// Insert other into self and return ``true`` iff self is changed
    pub fn coherent_insert(&mut self, p: Place<'tcx>, bb: BasicBlock) {
        if let Some(s) = &mut self.set {
            if let Some(self_p_bbs) = s.get_mut(&p) {
                self_p_bbs.extend(once(bb));
            } else {
                let mut new_bbs: FxHashSet<BasicBlock> = FxHashSet::default();
                new_bbs.extend(once(bb));
                s.insert(p.clone(), new_bbs);
            }
        } else {
            // Top is insertion-idempotent
        }
    }

    pub fn coherent_union(&mut self, other: &CondInitializedState<'mir, 'tcx>) {
        if let Some(s) = &mut self.set {
            if let Some(os) = &other.set {
                for (p, bb) in os.iter() {
                    if let Some(self_p_bbs) = s.get_mut(p) {
                        self_p_bbs.extend(bb);
                    } else {
                        s.insert(p.clone(), bb.clone());
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
    fn apply_operand_effect(&mut self, operand: &mir::Operand<'tcx>) {
        if let mir::Operand::Move(place) = operand {
            let ty = place.ty(&self.mir.local_decls, self.tcx).ty;
            let param_env = self.tcx.param_env(self.def_id);
            if !is_copy(self.tcx, ty, param_env) {
                self.coherent_kill(*place);
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
                        self.apply_operand_effect(operand);
                    }
                    mir::Rvalue::BinaryOp(_, box (ref operand1, ref operand2))
                    | mir::Rvalue::CheckedBinaryOp(_, box (ref operand1, ref operand2)) => {
                        self.apply_operand_effect(operand1);
                        self.apply_operand_effect(operand2);
                    }
                    mir::Rvalue::Aggregate(_, ref operands) => {
                        for operand in operands.iter() {
                            self.apply_operand_effect(operand);
                        }
                    }
                    _ => {}
                }

                self.coherent_insert(target, location.block);
            }
            mir::StatementKind::StorageDead(local) => {
                // https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/struct.Place.html
                // Each local naturally corresponds to the place Place { local, projection: [] }.
                // This place has the address of the local’s allocation and the type of the local.
                self.coherent_kill(Place {
                    local,
                    projection: rustc_middle::ty::List::empty(),
                });
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
                new_state.apply_operand_effect(discr);

                for &bb in terminator.successors() {
                    res_vec.push((bb, new_state.clone()));
                }
            }
            mir::TerminatorKind::Drop {
                place,
                target,
                unwind,
            } => {
                new_state.coherent_kill(place);
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
                new_state.coherent_kill(place);
                new_state.apply_operand_effect(value);
                new_state.coherent_insert(place, location.block);
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
                    new_state.apply_operand_effect(arg);
                }
                new_state.apply_operand_effect(func);
                if let Some((place, bb)) = destination {
                    new_state.coherent_insert(place, location.block);
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
                new_state.apply_operand_effect(cond);
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
                new_state.apply_operand_effect(value);
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
            for (p, bbs) in s.iter() {
                print!("\t\t{:#?}: ", p);
                for b in bbs.iter() {
                    print!("{:#?} ", b);
                }
                println!();
            }
        } else {
            println!("T");
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
            return s.is_empty();
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
