// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    analysis::AnalysisResult, serialization_utils::location_to_stmt_str, AbstractState, Analysis,
    AnalysisError,
};
use rustc_data_structures::{
    fingerprint::Fingerprint,
    fx::{FxHashMap, FxHashSet},
    stable_hasher::{HashStable, StableHasher},
};
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::def_id::DefId;
use serde::{ser::SerializeMap, Serialize, Serializer};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

pub struct ReachingDefsAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    mir: &'mir mir::Body<'tcx>,
}

/// A set of definition locations and function parameter indices per Local,
/// meaning that the Local might still have the value
/// which was assigned at the location or passed as a parameter
///
/// derived from prusti-interface/.../mir_analyses/liveness
#[derive(Clone)]
pub struct ReachingDefsState<'mir, 'tcx: 'mir> {
    // Local -> Location OR index of function parameter
    reaching_defs: FxHashMap<mir::Local, FxHashSet<DefLocation>>,
    mir: &'mir mir::Body<'tcx>, // just for context
    tcx: TyCtxt<'tcx>,
}

#[derive(Hash, Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefLocation {
    Assignment(mir::Location),
    /// The value is the index of the function parameter in ``mir.args_iter()``
    Parameter(usize),
}

impl<'mir, 'tcx: 'mir> ReachingDefsAnalysis<'mir, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, mir: &'mir mir::Body<'tcx>) -> Self {
        ReachingDefsAnalysis { tcx, def_id, mir }
    }
}

impl<'mir, 'tcx: 'mir> Analysis<'mir, 'tcx> for ReachingDefsAnalysis<'mir, 'tcx> {
    type State = ReachingDefsState<'mir, 'tcx>;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        self.mir
    }

    /// The bottom element of the lattice contains no definitions,
    /// i.e. all sets of reaching definitions are empty
    ///
    /// For a completely new bottom element we do not even insert any locals with sets into the map.
    fn new_bottom(&self) -> Self::State {
        ReachingDefsState {
            reaching_defs: FxHashMap::default(),
            mir: self.mir,
            tcx: self.tcx,
        }
    }

    fn new_initial(&self) -> Self::State {
        let mut reaching_defs: FxHashMap<mir::Local, FxHashSet<DefLocation>> = FxHashMap::default();
        // insert parameters
        for (idx, local) in self.mir.args_iter().enumerate() {
            let location_set = reaching_defs
                .entry(local)
                .or_insert_with(FxHashSet::default);
            location_set.insert(DefLocation::Parameter(idx));
        }
        ReachingDefsState {
            reaching_defs,
            mir: self.mir,
            tcx: self.tcx,
        }
    }

    fn need_to_widen(_counter: u32) -> bool {
        // only consider static information (assignments) => no lattice of infinite height
        false
    }

    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()> {
        state.apply_statement_effect(location)
    }

    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        state.apply_terminator_effect(location)
    }
}

impl<'mir, 'tcx: 'mir> fmt::Debug for ReachingDefsState<'mir, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // ignore mir
        f.debug_struct("ReachingDefsState")
            .field("reaching_defs", &self.reaching_defs)
            .finish()
    }
}

impl<'mir, 'tcx: 'mir> PartialEq for ReachingDefsState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        debug_assert_eq!(
            {
                let mut stable_hasher = StableHasher::new();
                self.mir.hash_stable(
                    &mut self.tcx.create_stable_hashing_context(),
                    &mut stable_hasher,
                );
                stable_hasher.finish::<Fingerprint>()
            },
            {
                let mut stable_hasher = StableHasher::new();
                other.mir.hash_stable(
                    &mut other.tcx.create_stable_hashing_context(),
                    &mut stable_hasher,
                );
                stable_hasher.finish::<Fingerprint>()
            },
        );
        // Ignore the `mir` field.
        self.reaching_defs == other.reaching_defs
    }
}
impl<'mir, 'tcx: 'mir> Eq for ReachingDefsState<'mir, 'tcx> {}

impl<'mir, 'tcx: 'mir> Serialize for ReachingDefsState<'mir, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut map = serializer.serialize_map(Some(self.reaching_defs.len()))?;
        let ordered_ass_map: BTreeMap<_, _> = self.reaching_defs.iter().collect();
        for (local, location_set) in ordered_ass_map {
            let ordered_loc_set: BTreeSet<_> = location_set.iter().collect();
            let mut location_vec = Vec::new();
            for location in ordered_loc_set {
                match location {
                    DefLocation::Assignment(l) => {
                        let stmt = location_to_stmt_str(*l, self.mir);
                        // Include the location to differentiate between same statement on
                        // different lines.
                        location_vec.push(format!("{:?}: {}", l, stmt));
                    }
                    DefLocation::Parameter(idx) => location_vec.push(format!("arg{}", idx)),
                }
            }
            map.serialize_entry(&format!("{:?}", local), &location_vec)?;
        }
        map.end()
    }
}

impl<'mir, 'tcx: 'mir> ReachingDefsState<'mir, 'tcx> {
    fn apply_statement_effect(&mut self, location: mir::Location) -> Result<(), AnalysisError> {
        let stmt = &self.mir[location.block].statements[location.statement_index];
        if let mir::StatementKind::Assign(box (ref target, _)) = stmt.kind {
            if let Some(local) = target.as_local() {
                let location_set = self
                    .reaching_defs
                    .entry(local)
                    .or_insert_with(FxHashSet::default);
                location_set.clear();
                location_set.insert(DefLocation::Assignment(location));
            }
        }

        Ok(())
    }

    fn apply_terminator_effect(
        &self,
        location: mir::Location,
    ) -> Result<Vec<(mir::BasicBlock, Self)>, AnalysisError> {
        let mut res_vec = Vec::new();
        let terminator = self.mir[location.block].terminator();
        match terminator.kind {
            mir::TerminatorKind::Call {
                ref destination,
                cleanup,
                ..
            } => {
                if let Some((place, bb)) = destination {
                    let mut dest_state = self.clone();
                    if let Some(local) = place.as_local() {
                        let location_set = dest_state
                            .reaching_defs
                            .entry(local)
                            .or_insert_with(FxHashSet::default);
                        location_set.clear();
                        location_set.insert(DefLocation::Assignment(location));
                    }
                    res_vec.push((*bb, dest_state));
                }

                if let Some(bb) = cleanup {
                    let mut cleanup_state = self.clone();
                    // error state -> be conservative & add destination as possible reaching def
                    // while keeping all others
                    if let Some((place, _)) = destination {
                        if let Some(local) = place.as_local() {
                            let location_set = cleanup_state
                                .reaching_defs
                                .entry(local)
                                .or_insert_with(FxHashSet::default);
                            location_set.insert(DefLocation::Assignment(location));
                        }
                    }
                    res_vec.push((bb, cleanup_state));
                }
            }
            mir::TerminatorKind::InlineAsm { .. } => {
                return Err(AnalysisError::UnsupportedStatement(location));
            }
            _ => {
                for &bb in terminator.successors() {
                    // no assignment -> no change of state
                    res_vec.push((bb, self.clone()));
                }
            }
        }

        Ok(res_vec)
    }
}

impl<'mir, 'tcx: 'mir> AbstractState for ReachingDefsState<'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        self.reaching_defs.iter().all(|(_, set)| set.is_empty())
    }

    fn join(&mut self, other: &Self) {
        for (local, other_locations) in other.reaching_defs.iter() {
            let location_set = self
                .reaching_defs
                .entry(*local)
                .or_insert_with(FxHashSet::default);
            location_set.extend(other_locations);
        }
    }

    fn widen(&mut self, _previous: &Self) {
        // assignments are static info => cannot grow infinitely => widening should not be needed
        unimplemented!()
    }
}
