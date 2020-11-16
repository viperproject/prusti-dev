// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module provides the reaching definitions analysis state for MIR.
//!
//! For each program point it stores which assignments to local
//! variables MAY reach that program point.
//! derived from mir_analyses/liveness

use std::collections::{HashMap, HashSet, BTreeMap, BTreeSet};
use crate::{AbstractState, AnalysisError};
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use serde::{Serialize, Serializer};
use serde::ser::SerializeMap;


/*#[derive(PartialEq, Eq, Hash, Copy, Clone, Ord, PartialOrd)]
pub struct Assignment {
    pub target: mir::Local,
    pub location: mir::Location,
}

impl fmt::Debug for Assignment {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}={:?}", self.target, self.location)
    }
}*/

#[derive(Clone, Debug)]
pub struct ReachingDefsState<'a, 'tcx: 'a> {
    reaching_assignments: HashMap<mir::Local, HashSet<mir::Location>>,
    mir: &'a mir::Body<'tcx>,   // just a helper
}

impl<'a, 'tcx: 'a> PartialEq for ReachingDefsState<'a, 'tcx> {      // manual implementation needed, because not implemented for Body
    fn eq(&self, other: &Self) -> bool {
        self.reaching_assignments == other.reaching_assignments
        // ignore Body
    }
}
impl<'a, 'tcx: 'a> Eq for ReachingDefsState<'a, 'tcx> {}


impl<'a, 'tcx: 'a> Serialize for ReachingDefsState<'a, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut map = serializer.serialize_map(Some(self.reaching_assignments.len()))?;
        let ordered_ass_map: BTreeMap<_, _> = self.reaching_assignments.iter().collect();
        for (local, locations) in ordered_ass_map {
            let ordered_loc_set: BTreeSet<_> = locations.iter().collect();
            let mut location_vec = Vec::new();
            for location in ordered_loc_set {
                let stmt = &self.mir[location.block].statements[location.statement_index];
                location_vec.push(format!("{:?}: {:?}", location, stmt));       // keep location for differentiation between same statement on different lines
            }
            map.serialize_entry(&format!("{:?}", local), &location_vec)?;
        }
        map.end()
    }
}

impl<'a, 'tcx: 'a> AbstractState<'a, 'tcx> for ReachingDefsState<'a, 'tcx> {
    fn new_bottom(mir: &'a mir::Body<'tcx>, _tcx: TyCtxt<'tcx>) -> Self {
        Self {
            reaching_assignments: HashMap::new(),
            mir,
        }
    }

    fn new_initial(mir: &'a mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {     //TODO: also interpret argument passing as definition?
        Self::new_bottom(mir, tcx)
    }

    fn need_to_widen(_counter: &u32) -> bool {
        false       // only consider static information (assignments) => no lattice of infinite height
    }

    fn join(&mut self, other: &Self) {
        for (local, other_assignments) in other.reaching_assignments.iter() {
            let assignments = self.reaching_assignments.entry(*local).or_insert(HashSet::new());
            for assignment in other_assignments.iter() {
                assignments.insert(*assignment);
            }
        }
    }

    fn widen(&mut self, _previous: &Self) {
        // assignments are static info -> cannot grow infinitely -> widening should not be needed
        unimplemented!()
    }

    fn apply_statement_effect(&mut self, location: &mir::Location, mir: &mir::Body<'tcx>)
        -> Result<(), AnalysisError> {

        let stmt = &mir[location.block].statements[location.statement_index];
        match stmt.kind {
            mir::StatementKind::Assign(box (ref target, _)) => {
                if let Some(local) = target.as_local() {
                    let assignment_set = self.reaching_assignments.entry(local).or_insert(HashSet::new());
                    assignment_set.clear();
                    assignment_set.insert(*location);
                }
                Ok(())
            }
            //TODO: StorageDead -> remove def?
            _ => {Ok(())}
        }
    }

    fn apply_terminator_effect(&self, location: &mir::Location, mir: &mir::Body<'tcx>)
        -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {

        let terminator = mir[location.block].terminator();
        match terminator.kind {
            mir::TerminatorKind::Call {
                ref destination, cleanup, ..
            } => {
                let mut res_vec = Vec::new();
                if let Some((place, bb)) = destination {
                    let mut dest_state = self.clone();
                    if let Some(local) = place.as_local() {
                        let assignment_set = dest_state.reaching_assignments.entry(local).or_insert(HashSet::new());
                        assignment_set.clear();
                        assignment_set.insert(*location);
                    }
                    res_vec.push((*bb, dest_state));
                }
                if let Some(bb) = cleanup {
                    //TODO: correct? assignment failed?
                    res_vec.push((bb, self.clone()));
                }
                Ok(res_vec)
            }
            _ => {
                let mut res_vec = Vec::new();
                for bb in terminator.successors() {
                    // no assignment -> no change of state
                    res_vec.push((*bb, self.clone()));
                }
                Ok(res_vec)
            }
        }
    }
}
