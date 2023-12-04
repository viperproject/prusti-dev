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
    coupling_graph::{
        outlives_info::edge::{Edge, EdgeKind, EdgeOrigin},
        CgContext,
    },
    free_pcs::{
        engine::FreePlaceCapabilitySummary, CapabilityLocal, CapabilityProjections, RepackOp,
    },
    utils::{Place, PlaceRepacker},
};

use super::engine::CouplingGraph;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Graph<'tcx> {
    pub nodes: IndexVec<RegionVid, Node<'tcx>>,
    // Regions equal to 'static
    pub static_regions: FxHashSet<RegionVid>,
    // Two-phase loans waiting to activate
    pub inactive_loans: FxHashSet<RegionVid>,
}

impl<'tcx> Graph<'tcx> {
    #[tracing::instrument(name = "Graph::outlives", level = "trace", skip(self), ret)]
    pub fn outlives(&mut self, edge: Edge<'tcx>) -> Option<(RegionVid, RegionVid, bool)> {
        self.outlives_inner(vec![edge])
    }
    // #[tracing::instrument(name = "Graph::outlives_placeholder", level = "trace", skip(self), ret)]
    // pub fn outlives_placeholder(&mut self, sup: RegionVid, sub: RegionVid, origin: EdgeOrigin) -> Option<(RegionVid, RegionVid)> {
    //     let edge = EdgeInfo::no_reason(sup, sub, None, origin);
    //     self.outlives_inner(vec![edge])
    // }

    // sup outlives sub, or `sup: sub` (i.e. sup gets blocked)
    #[tracing::instrument(name = "Graph::outlives_inner", level = "trace", skip(self), ret)]
    fn outlives_inner(&mut self, edge: Vec<Edge<'tcx>>) -> Option<(RegionVid, RegionVid, bool)> {
        let (sup, sub) = self.outlives_unwrap_edge(&edge);
        self.nodes[sup].blocked_by.insert(sub);
        let blocks = self.nodes[sub].blocks.entry(sup).or_default();
        let is_blocking = edge.iter().any(|edge| edge.kind.is_blocking());
        if blocks.insert(edge) {
            Some((sup, sub, is_blocking))
        } else {
            None
        }
    }
    fn outlives_unwrap_edge(&mut self, edge: &Vec<Edge<'tcx>>) -> (RegionVid, RegionVid) {
        let (sup, sub) = (edge.last().unwrap().sup(), edge.first().unwrap().sub());
        if self.static_regions.contains(&sub) {
            Self::set_static_region(&self.nodes, &mut self.static_regions, sup);
        }
        (sup, sub)
    }

    // sup outlives sub, or `sup: sub` (i.e. sup gets blocked)
    #[tracing::instrument(name = "Graph::outlives_join", level = "trace", skip(self), ret)]
    pub(super) fn outlives_join(
        &mut self,
        edge: Vec<Edge<'tcx>>,
    ) -> Option<(RegionVid, RegionVid)> {
        let (sup, sub) = self.outlives_unwrap_edge(&edge);
        self.nodes[sup].blocked_by.insert(sub);
        let blocks = self.nodes[sub].blocks.entry(sup).or_default();

        if blocks
            .iter()
            .any(|other| Edge::generalized_by(&edge, other))
        {
            None
        } else {
            blocks.retain(|other| !Edge::generalized_by(other, &edge));
            if blocks.insert(edge) {
                Some((sup, sub))
            } else {
                None
            }
        }
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
    pub fn kill_borrow(&mut self, data: &BorrowData<'tcx>) -> Vec<RegionVid> {
        self.kill(data.region)
    }

    #[tracing::instrument(name = "Graph::kill", level = "trace", skip(self))]
    fn kill(&mut self, r: RegionVid) -> Vec<RegionVid> {
        assert!(!self.static_regions.contains(&r));
        let (_, blocked_by) = self.remove_all_edges(r);
        [r].into_iter()
            .chain(
                blocked_by
                    .iter()
                    .flat_map(|(blocked_by, _)| self.kill(*blocked_by)),
            )
            .collect()
    }

    #[tracing::instrument(name = "Graph::remove", level = "trace", ret)]
    /// Remove node from graph and rejoin all blockers and blocked by.
    // Set `remove_dangling_children` when removing regions which are not tracked by the regular borrowck,
    // to remove in e.g. `let y: &'a i32 = &'b *x;` the region `'b` when removing `'a` (if `x: &'c i32`).
    // NOTE: Maybe shouldn't be set, since it seems that the regular borrowck does not kill off `'b` this eagerly (if `x: &'c mut i32`).
    pub fn remove(
        &mut self,
        r: RegionVid,
    ) -> Option<(RegionVid, Vec<(RegionVid, RegionVid, bool)>)> {
        let (blocks, blocked_by) = self.remove_all_edges(r);
        let changed = !(blocks.is_empty() && blocked_by.is_empty());
        let mut rejoins = Vec::new();
        for (sup, sup_reasons) in blocks {
            for (&sub, sub_reasons) in &blocked_by {
                // Do not rejoin nodes in a loop to themselves
                if sub != sup {
                    // TODO: change this so that we do not need to make opaque
                    assert!(sup_reasons.len() * sub_reasons.len() < 100);
                    let mut rejoined = None;
                    for sup_reason in &sup_reasons {
                        for sub_reason in sub_reasons {
                            let reasons = sub_reason.iter().chain(sup_reason).copied().collect();
                            let new = self.outlives_inner(reasons);
                            if new.is_some() {
                                rejoined = new;
                            }
                        }
                    }
                    if let Some(rejoined) = rejoined {
                        rejoins.push(rejoined);
                    }
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
        if changed {
            Some((r, rejoins))
        } else {
            None
        }
    }

    #[tracing::instrument(name = "Graph::remove_many", level = "trace")]
    pub fn remove_many(
        &mut self,
        rs: &FxHashSet<RegionVid>,
    ) -> Vec<(RegionVid, Vec<(RegionVid, RegionVid, bool)>)> {
        for &r in rs {
            if self.predecessors(r).iter().all(|pre| rs.contains(pre))
                || self.successors(r).iter().all(|suc| rs.contains(suc))
            {
                self.static_regions.remove(&r);
                self.remove_all_edges(r);
            }
        }
        rs.iter().flat_map(|r| self.remove(*r)).collect()
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
        FxHashMap<RegionVid, FxHashSet<Vec<Edge<'tcx>>>>,
        FxHashMap<RegionVid, FxHashSet<Vec<Edge<'tcx>>>>,
    ) {
        let blocks = std::mem::replace(&mut self.nodes[r].blocks, FxHashMap::default());
        for block in blocks.keys() {
            self.nodes[*block].blocked_by.remove(&r);
        }
        let blocked_by = std::mem::replace(&mut self.nodes[r].blocked_by, FxHashSet::default());
        let blocked_by = blocked_by
            .into_iter()
            .map(|bb| (bb, self.nodes[bb].blocks.remove(&r).unwrap()))
            .collect();
        (blocks, blocked_by)
    }

    fn predecessors(&self, r: RegionVid) -> FxHashSet<RegionVid> {
        let mut predecessors = FxHashSet::default();
        self.predecessors_helper(r, &mut predecessors);
        predecessors
    }
    fn predecessors_helper(&self, r: RegionVid, visited: &mut FxHashSet<RegionVid>) {
        let tp: Vec<_> = self.nodes[r]
            .blocked_by
            .iter()
            .copied()
            .filter(|r| visited.insert(*r))
            .collect();
        for r in tp {
            self.predecessors_helper(r, visited)
        }
    }
    fn successors(&self, r: RegionVid) -> FxHashSet<RegionVid> {
        let mut successors = FxHashSet::default();
        self.successors_helper(r, &mut successors);
        successors
    }
    fn successors_helper(&self, r: RegionVid, visited: &mut FxHashSet<RegionVid>) {
        let tp: Vec<_> = self.nodes[r]
            .blocks
            .iter()
            .map(|(r, _)| *r)
            .filter(|r| visited.insert(*r))
            .collect();
        for r in tp {
            self.successors_helper(r, visited)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node<'tcx> {
    pub blocks: FxHashMap<RegionVid, FxHashSet<Vec<Edge<'tcx>>>>,
    pub blocked_by: FxHashSet<RegionVid>,
}

impl<'tcx> Node<'tcx> {
    pub fn new() -> Self {
        Self {
            blocks: FxHashMap::default(),
            blocked_by: FxHashSet::default(),
        }
    }
    pub fn true_edges(&self) -> Vec<RegionVid> {
        self.blocks
            .iter()
            .filter(|(_, edges)| edges.iter().any(|edge| Edge::is_blocking(edge)))
            .map(|(&r, _)| r)
            .collect()
    }
}
