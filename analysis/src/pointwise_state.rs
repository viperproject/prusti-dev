// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{data_structures::fx::FxHashMap, middle::mir};
use serde::{ser::SerializeMap, Serialize, Serializer};
use std::{collections::BTreeMap, fmt};

/// Records the state of the analysis at every program point and CFG edge of `mir`.
pub struct PointwiseState<'mir, 'tcx: 'mir, S: Serialize> {
    state_before: FxHashMap<mir::Location, S>,
    /// Maps each basic block to a map of its successor blocks to the state on the CFG edge.
    state_after_block: FxHashMap<mir::BasicBlock, FxHashMap<mir::BasicBlock, S>>,
    // Needed for translation of location to statement/terminator in serialization.
    pub(crate) mir: &'mir mir::Body<'tcx>,
}

impl<'mir, 'tcx: 'mir, S> fmt::Debug for PointwiseState<'mir, 'tcx, S>
where
    S: Serialize + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // ignore tcx
        f.debug_struct("PointwiseState")
            .field("state_before", &self.state_before)
            .field("state_after_block", &self.state_after_block)
            .field("mir", &self.mir)
            .finish()
    }
}

impl<'mir, 'tcx: 'mir, S: Serialize> Serialize for PointwiseState<'mir, 'tcx, S> {
    /// Serialize PointwiseState by translating it to a combination of vectors, tuples and maps,
    /// such that serde can automatically translate it.
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut map = serializer.serialize_map(Some(self.mir.basic_blocks.len()))?;

        for bb in self.mir.basic_blocks.indices() {
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            let mut stmt_vec: Vec<_> = Vec::with_capacity(statements.len());
            for (statement_index, stmt) in statements.iter().enumerate() {
                let location = mir::Location {
                    block: bb,
                    statement_index,
                };
                let state = self.lookup_before(location).unwrap();

                // output statement
                stmt_vec.push(("state:", state, format!("statement: {stmt:?}")));
            }

            let term_location = self.mir.terminator_loc(bb);
            let state_before = self.lookup_before(term_location).unwrap();

            let terminator_str = format!("terminator: {:?}", self.mir[bb].terminator().kind);

            let new_map = FxHashMap::default();
            let map_after = self.lookup_after_block(bb).unwrap_or(&new_map);
            let ordered_succ_map: BTreeMap<_, _> = map_after
                .iter()
                .map(|(bb, s)| (format!("{bb:?}"), ("state:", s)))
                .collect();

            map.serialize_entry(
                &format!("{bb:?}"),
                &(
                    stmt_vec,
                    "state before terminator:",
                    state_before,
                    terminator_str,
                    ordered_succ_map,
                ),
            )?;
        }
        map.end()
    }
}

impl<'mir, 'tcx: 'mir, S: Serialize> PointwiseState<'mir, 'tcx, S> {
    pub fn new(mir: &'mir mir::Body<'tcx>) -> Self {
        Self {
            state_before: FxHashMap::default(),
            state_after_block: FxHashMap::default(),
            mir,
        }
    }

    /// Look up the state before the `location`.
    /// The `location` can point to a statement or terminator.
    pub fn lookup_before(&self, location: mir::Location) -> Option<&S> {
        self.state_before.get(&location)
    }

    /// Look up the mutable state before the `location`.
    /// The `location` can point to a statement or terminator.
    pub fn lookup_mut_before(&mut self, location: mir::Location) -> Option<&mut S> {
        self.state_before.get_mut(&location)
    }

    /// Look up the state after the `location`.
    /// The `location` should point to a statement, not a terminator.
    pub fn lookup_after(&self, location: mir::Location) -> Option<&S> {
        debug_assert!(location.statement_index < self.mir[location.block].statements.len());
        self.state_before.get(&location.successor_within_block())
    }

    /// Look up the state on the outgoing CFG edges of `block`.
    /// The return value maps all successor blocks to the state on the CFG edge from `block` to
    /// that block.
    pub fn lookup_after_block(
        &self,
        block: mir::BasicBlock,
    ) -> Option<&FxHashMap<mir::BasicBlock, S>> {
        self.state_after_block.get(&block)
    }

    /// Return the mutable state of the analysis on the outgoing CFG edges of `block`.
    /// The return value maps all successor blocks to the state on the CFG edge from `block` to
    /// that block.
    pub(crate) fn lookup_mut_after_block(
        &mut self,
        block: mir::BasicBlock,
    ) -> &mut FxHashMap<mir::BasicBlock, S> {
        self.state_after_block.entry(block).or_default()
    }

    /// Update the state before the `location`.
    /// The `location` can point to a statement or terminator.
    pub(crate) fn set_before(&mut self, location: mir::Location, state: S) {
        self.state_before.insert(location, state);
    }
}

impl<'mir, 'tcx: 'mir, S: Serialize + Default> PointwiseState<'mir, 'tcx, S> {
    pub fn default(mir: &'mir mir::Body<'tcx>) -> Self {
        let state_before: FxHashMap<_, _> = mir
            .basic_blocks
            .iter_enumerated()
            .flat_map(|(block, bb_data)| {
                (0..=bb_data.statements.len()).map(move |statement_index| {
                    (
                        mir::Location {
                            block,
                            statement_index,
                        },
                        S::default(),
                    )
                })
            })
            .collect();
        let state_after_block: FxHashMap<_, _> = mir
            .basic_blocks
            .iter_enumerated()
            .map(|(block, bb_data)| {
                let successors: FxHashMap<_, _> = bb_data
                    .terminator()
                    .successors()
                    .map(|successor| (successor, S::default()))
                    .collect();
                (block, successors)
            })
            .collect();
        Self {
            state_before,
            state_after_block,
            mir,
        }
    }
}
