// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    borrow::Cow,
    fmt::{Debug, Display, Formatter, Result},
};

use derive_more::{Deref, DerefMut};
use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    borrowck::{
        borrow_set::BorrowData,
        consumers::{BorrowIndex, OutlivesConstraint},
    },
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    dataflow::fmt::DebugWithContext,
    index::{bit_set::BitSet, IndexVec},
    middle::{
        mir::{BasicBlock, ConstraintCategory, Local, Location, Operand, RETURN_PLACE},
        ty::{RegionVid, TyKind},
    },
};

use crate::{
    coupling_graph::{region_place::PlaceRegion, CgContext},
    free_pcs::{
        engine::FreePlaceCapabilitySummary, CapabilityLocal, CapabilityProjections, RepackOp,
    },
    utils::{Place, PlaceRepacker},
};

use super::engine::CoupligGraph;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Graph<'tcx> {
    pub nodes: IndexVec<RegionVid, Node<'tcx>>,
    // Regions equal to 'static
    pub static_regions: FxHashSet<RegionVid>,
}

impl<'tcx> Graph<'tcx> {
    #[tracing::instrument(name = "Graph::outlives", level = "trace", skip(self), ret)]
    pub fn outlives(&mut self, c: OutlivesConstraint<'tcx>) -> bool {
        let edge = EdgeInfo {
            creation: c.locations.from_location(),
            reason: Some(c.category),
        };
        self.outlives_inner(c.sup, c.sub, edge)
    }
    pub fn outlives_static(&mut self, r: RegionVid, static_region: RegionVid, l: Location) {
        if r == static_region {
            return;
        }
        let edge = EdgeInfo {
            creation: Some(l),
            reason: None,
        };
        self.outlives_inner(r, static_region, edge);
    }
    pub fn outlives_placeholder(&mut self, sup: RegionVid, sub: RegionVid) -> bool {
        let edge = EdgeInfo {
            creation: None,
            reason: None,
        };
        self.outlives_inner(sup, sub, edge)
    }

    // sup outlives sub, or `sup: sub` (i.e. sup gets blocked)
    #[tracing::instrument(name = "Graph::outlives", level = "trace", skip(self), ret)]
    pub(crate) fn outlives_inner(
        &mut self,
        sup: RegionVid,
        sub: RegionVid,
        edge: EdgeInfo<'tcx>,
    ) -> bool {
        if sup == sub {
            panic!();
            return false;
        }
        if self.static_regions.contains(&sub) {
            Self::set_static_region(&self.nodes, &mut self.static_regions, sup);
        }
        self.nodes[sup]
            .blocked_by
            .entry(sub)
            .or_default()
            .insert(edge);
        self.nodes[sub].blocks.entry(sup).or_default().insert(edge)
    }
    fn set_static_region(
        nodes: &IndexVec<RegionVid, Node<'tcx>>,
        static_regions: &mut FxHashSet<RegionVid>,
        r: RegionVid,
    ) {
        if static_regions.insert(r) {
            for &sup in nodes[r].blocks.keys() {
                Self::set_static_region(nodes, static_regions, sup);
            }
        }
    }

    #[tracing::instrument(name = "Graph::kill_borrow", level = "debug", skip(self))]
    /// Remove borrow from graph and all nodes that block it and the node it blocks
    pub fn kill_borrow(&mut self, data: &BorrowData<'tcx>) {
        self.kill(data.region);
    }

    #[tracing::instrument(name = "Graph::kill", level = "trace", skip(self))]
    fn kill(&mut self, r: RegionVid) {
        assert!(!self.static_regions.contains(&r));
        let (_, blocked_by) = self.remove_all_edges(r);
        for (blocked_by, _) in blocked_by {
            self.kill(blocked_by);
        }
    }

    #[tracing::instrument(name = "Graph::remove", level = "trace")]
    /// Remove node from graph and rejoin all blockers and blocked by.
    // Set `remove_dangling_children` when removing regions which are not tracked by the regular borrowck,
    // to remove in e.g. `let y: &'a i32 = &'b *x;` the region `'b` when removing `'a` (if `x: &'c i32`).
    // NOTE: Maybe shouldn't be set, since it seems that the regular borrowck does not kill off `'b` this eagerly (if `x: &'c mut i32`).
    pub fn remove(&mut self, r: RegionVid, l: Option<Location>) -> bool {
        let (blocks, blocked_by) = self.remove_all_edges(r);
        let changed = !(blocks.is_empty() && blocked_by.is_empty());
        for &block in blocks.keys() {
            for &blocked_by in blocked_by.keys() {
                // Do not rejoin nodes in a loop to themselves
                if blocked_by != block {
                    let edge = EdgeInfo {
                        creation: l,
                        reason: None,
                    };
                    self.outlives_inner(block, blocked_by, edge);
                }
            }
            // if remove_dangling_children {
            //     let node = &self.nodes[block];
            //     if node.blocked_by.is_empty() && self.cgx.sbs.location_map.values().any(|data| data.region == block) {
            //         self.remove(block, l, false, remove_dangling_children);
            //     }
            // }
        }
        let was_static = self.static_regions.remove(&r);
        debug_assert!(!was_static || changed); // Check that `was_static ==> changed`
        changed
    }

    pub(crate) fn all_nodes(&self) -> impl Iterator<Item = (RegionVid, &Node<'tcx>)> {
        self.nodes
            .iter_enumerated()
            .filter(|(_, n)| !n.blocked_by.is_empty() || !n.blocks.is_empty())
    }

    fn remove_all_edges(
        &mut self,
        r: RegionVid,
    ) -> (
        FxHashMap<RegionVid, FxHashSet<EdgeInfo<'tcx>>>,
        FxHashMap<RegionVid, FxHashSet<EdgeInfo<'tcx>>>,
    ) {
        let blocks = std::mem::replace(&mut self.nodes[r].blocks, FxHashMap::default());
        for block in blocks.keys() {
            self.nodes[*block].blocked_by.remove(&r);
        }
        let blocked_by = std::mem::replace(&mut self.nodes[r].blocked_by, FxHashMap::default());
        for block_by in blocked_by.keys() {
            self.nodes[*block_by].blocks.remove(&r);
        }
        (blocks, blocked_by)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node<'tcx> {
    pub blocks: FxHashMap<RegionVid, FxHashSet<EdgeInfo<'tcx>>>,
    pub blocked_by: FxHashMap<RegionVid, FxHashSet<EdgeInfo<'tcx>>>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct EdgeInfo<'tcx> {
    pub creation: Option<Location>,
    pub reason: Option<ConstraintCategory<'tcx>>,
}

impl Display for EdgeInfo<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let reason = if let Some(reason) = self.reason {
            match reason {
                ConstraintCategory::Return(_) => "return",
                ConstraintCategory::Yield => "yield",
                ConstraintCategory::UseAsConst => "const",
                ConstraintCategory::UseAsStatic => "static",
                ConstraintCategory::TypeAnnotation => "type",
                ConstraintCategory::Cast => "cast",
                ConstraintCategory::ClosureBounds => "closure",
                ConstraintCategory::CallArgument(_) => "arg",
                ConstraintCategory::CopyBound => "copy",
                ConstraintCategory::SizedBound => "sized",
                ConstraintCategory::Assignment => "assign",
                ConstraintCategory::Usage => "use",
                ConstraintCategory::OpaqueType => "opaque",
                ConstraintCategory::ClosureUpvar(_) => "upvar",
                ConstraintCategory::Predicate(_) => "pred",
                ConstraintCategory::Boring => "?",
                ConstraintCategory::BoringNoLocation => "? no_loc",
                ConstraintCategory::Internal => "internal",
            }
        } else {
            "other"
        };
        let creation = self
            .creation
            .map(|c| format!("{c:?}"))
            .unwrap_or_else(|| "sig".to_string());
        write!(f, "{creation} ({reason})")
    }
}

impl<'tcx> Node<'tcx> {
    pub fn new() -> Self {
        Self {
            blocks: FxHashMap::default(),
            blocked_by: FxHashMap::default(),
        }
    }
}
