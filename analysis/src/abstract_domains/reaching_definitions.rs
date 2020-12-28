// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;
use std::collections::{HashMap, HashSet, BTreeMap, BTreeSet};
use crate::{AbstractState, AnalysisError};
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use serde::{Serialize, Serializer};
use serde::ser::SerializeMap;
use crate::serialization_utils::location_to_stmt_str;
use serde::export::Formatter;


/// A set of definition locations and function parameter indices per Local,
/// meaning that the Local might still have the value
/// which was assigned at the location or passed as a parameter
///
/// derived from prusti-interface/.../mir_analyses/liveness
#[derive(Clone)]
pub struct ReachingDefsState<'a, 'tcx: 'a> {
    // Local -> Location OR index of function parameter
    reaching_assignments: HashMap<mir::Local, HashSet<Result<mir::Location, usize>>>,
    mir: &'a mir::Body<'tcx>,   // just for context
}

impl<'a, 'tcx: 'a> fmt::Debug for ReachingDefsState<'a, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // ignore mir
        f.debug_struct("ReachingDefsState")
            .field("reaching_assignments", &self.reaching_assignments)
            .finish()
    }
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
        for (local, location_set) in ordered_ass_map {
            let ordered_loc_set: BTreeSet<_> = location_set.iter().collect();
            let mut location_vec = Vec::new();
            for location in ordered_loc_set {
                match location {
                    Ok(l) => {
                        let stmt = location_to_stmt_str(l, self.mir);
                        location_vec.push(format!("{:?}: {}", l, stmt));
                    },             // keep location for differentiation between same statement on different lines
                    Err(idx) => location_vec.push(format!("arg{}", idx))
                }
            }
            map.serialize_entry(&format!("{:?}", local), &location_vec)?;
        }
        map.end()
    }
}

impl<'a, 'tcx: 'a> AbstractState<'a, 'tcx> for ReachingDefsState<'a, 'tcx> {

    /// all sets are empty
    fn new_bottom(mir: &'a mir::Body<'tcx>, _tcx: TyCtxt<'tcx>) -> Self {
        Self {
            reaching_assignments: HashMap::new(),
            mir,
        }
    }

    fn is_bottom(&self) -> bool {
        self.reaching_assignments.iter().all(|(_, set)| set.is_empty())
    }

    fn new_initial(mir: &'a mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let mut reaching_assignments: HashMap<mir::Local, HashSet<Result<mir::Location, usize>>> = HashMap::new();
        // insert parameters
        for (idx, local) in mir.args_iter().enumerate() {
            let location_set = reaching_assignments.entry(local).or_insert(HashSet::new());
            location_set.insert(Err(idx));
        }
        Self {
            reaching_assignments,
            mir,
        }
    }

    fn need_to_widen(_counter: &u32) -> bool {
        false       // only consider static information (assignments) => no lattice of infinite height
    }

    fn join(&mut self, other: &Self) {
        for (local, other_locations) in other.reaching_assignments.iter() {
            let location_set = self.reaching_assignments.entry(*local).or_insert(HashSet::new());
            location_set.extend(other_locations);
        }
    }

    fn widen(&mut self, _previous: &Self) {
        // assignments are static info => cannot grow infinitely => widening should not be needed
        unimplemented!()
    }

    fn apply_statement_effect(&mut self, location: &mir::Location)
        -> Result<(), AnalysisError> {

        let stmt = &self.mir[location.block].statements[location.statement_index];
        match stmt.kind {
            mir::StatementKind::Assign(box (ref target, _)) => {
                if let Some(local) = target.as_local() {
                    let location_set = self.reaching_assignments.entry(local).or_insert(HashSet::new());
                    location_set.clear();
                    location_set.insert(Ok(*location));
                }
                Ok(())
            }
            _ => {Ok(())}
        }
    }

    fn apply_terminator_effect(&self, location: &mir::Location)
        -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {

        let mut res_vec = Vec::new();
        let terminator = self.mir[location.block].terminator();
        match terminator.kind {
            mir::TerminatorKind::Call {
                ref destination, cleanup, ..
            } => {
                if let Some((place, bb)) = destination {
                    let mut dest_state = self.clone();
                    if let Some(local) = place.as_local() {
                        let location_set = dest_state.reaching_assignments.entry(local).or_insert(HashSet::new());
                        location_set.clear();
                        location_set.insert(Ok(*location));
                    }
                    res_vec.push((*bb, dest_state));
                }

                if let Some(bb) = cleanup {
                    let mut cleanup_state = self.clone();
                    // error state -> be conservative & add destination as possible reaching def while keeping all others
                    if let Some((place, _)) = destination {
                        if let Some(local) = place.as_local() {
                            let location_set = cleanup_state.reaching_assignments.entry(local).or_insert(HashSet::new());
                            location_set.insert(Ok(*location));
                        }
                    }
                    res_vec.push((bb, cleanup_state));
                }
            }
            mir::TerminatorKind::InlineAsm { .. }  =>
                return Err(AnalysisError::UnsupportedStatement(*location)),

            _ => {
                for bb in terminator.successors() {
                    // no assignment -> no change of state
                    res_vec.push((*bb, self.clone()));
                }
            }
        }

        Ok(res_vec)
    }
}
