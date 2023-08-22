// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{fmt::{Debug, Formatter, Result}, borrow::Cow};

use derive_more::{Deref, DerefMut};
use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    index::bit_set::BitSet,
    dataflow::fmt::DebugWithContext, index::IndexVec, middle::mir::Local,
    borrowck::{borrow_set::BorrowData, consumers::BorrowIndex},
    middle::{mir::ConstraintCategory, ty::{RegionVid, TyKind}},
};

use crate::{
    free_pcs::{
        engine::FreePlaceCapabilitySummary, CapabilityLocal, CapabilityProjections, RepackOp,
    },
    utils::{PlaceRepacker, Place},
};

use super::engine::CoupligGraph;

#[derive(Clone)]
pub struct Regions<'a, 'tcx> {
    pub borrows: FxHashMap<BorrowIndex, (Vec<RegionVid>, Vec<(Local, RegionVid)>)>,
    pub(crate) subset: Vec<(RegionVid, RegionVid)>,
    pub(crate) graph: Graph<'a, 'tcx>,
}

pub type NodeId = usize;

#[derive(Clone)]
pub struct Graph<'a, 'tcx> {
    pub rp: PlaceRepacker<'a, 'tcx>,
    pub facts: &'a BorrowckFacts,
    pub facts2: &'a BorrowckFacts2<'tcx>,
    pub nodes: Vec<Option<Node<'tcx>>>,
    pub skip_empty_nodes: bool,
    pub shared_borrows: Vec<BorrowData<'tcx>>,
}

impl PartialEq for Graph<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.nodes == other.nodes
    }
}

impl<'a, 'tcx> Graph<'a, 'tcx> {
    pub fn new(rp: PlaceRepacker<'a, 'tcx>, facts: &'a BorrowckFacts, facts2: &'a BorrowckFacts2<'tcx>) -> Self {
        let mut result = Self {
            rp,
            facts,
            facts2,
            nodes: Vec::new(),
            skip_empty_nodes: false,
            shared_borrows: Vec::new(),
        };
        // let input_facts = facts.input_facts.borrow();
        // for &(r1, r2) in &input_facts.as_ref().unwrap().known_placeholder_subset {
        //     result.outlives(r1, r2);
        // }
        let constraints = facts2.region_inference_context.outlives_constraints();
        for c in constraints {
            if c.locations.from_location().is_none() {
                result.outlives(c.sup, c.sub, c.category);
            }
        }
        result
    }
    pub fn new_shared_borrow(&mut self, data: BorrowData<'tcx>) {
        self.shared_borrows.push(data);
    }
    pub fn outlives(&mut self, r1: RegionVid, r2: RegionVid, reason: ConstraintCategory<'tcx>) {
        let n1 = self.region_to_node(r1);
        let n2 = self.region_to_node(r2);
        if n1 == n2 {
            return;
        }
        // println!("Adding outlives {r1:?} ({n1}): {r2:?} ({n2})");
        if let Some(path) = self.reachable(n1, n2) {
            for other in path {
                self.merge(other, n2);
            }
        } else {
            self.blocks(n2, n1, reason);
        }
    }
    // pub fn contained_by(&mut self, r: RegionVid, l: Local) {
    //     let n = self.region_to_node(r);
    //     self.get_node_mut(n).contained_by.push(l);
    // }
    pub fn kill(&mut self, r: RegionVid) {
        let n = self.region_to_node(r);
        self.kill_node(n)
    }
    pub fn remove(&mut self, r: RegionVid, maybe_already_removed: bool) {
        for n in self.nodes.iter_mut() {
            if let Some(n) = n {
                if n.regions.contains(&r) {
                    n.regions.remove(&r);
                    if n.regions.is_empty() {
                        let id = n.id;
                        let n = self.remove_node(id);
                        for (&block, _) in &n.blocks {
                            for (&blocked_by, &edge) in &n.blocked_by {
                                self.blocks(blocked_by, block, edge.reason);
                            }
                        }
                    }
                    return;
                }
            }
        }
        assert!(maybe_already_removed, "Region {:?} not found in graph", r);
    }

    fn reachable(&self, from: NodeId, to: NodeId) -> Option<FxHashSet<NodeId>> {
        // println!("Checking reachability from {} to {}", from, to);
        let mut nodes = FxHashSet::default();
        if from == to {
            return Some(nodes);
        }
        for (&next, _) in &self.get_node(from).blocks {
            if let Some(others) = self.reachable(next, to) {
                nodes.insert(from);
                nodes.extend(others);
            }
        }
        if nodes.is_empty() {
            None
        } else {
            Some(nodes)
        }
    }
    fn region_to_node(&mut self, r: RegionVid) -> NodeId {
        let mut last_none = self.nodes.len();
        for (i, n) in self.nodes.iter().enumerate() {
            if let Some(n) = n {
                if n.regions.contains(&r) {
                    return i;
                }
            } else {
                last_none = i;
            }
        }
        if last_none == self.nodes.len() {
            self.nodes.push(Some(Node::new(last_none, r)));
        } else {
            self.nodes[last_none] = Some(Node::new(last_none, r));
        }
        last_none
    }
    fn merge(&mut self, n1: NodeId, n2: NodeId) {
        assert_ne!(n1, n2);
        let to_merge = self.remove_node(n1);
        for (block, edge) in to_merge.blocks {
            if block != n2 {
                self.blocks(n2, block, edge.reason);
            }
        }
        for (block_by, edge) in to_merge.blocked_by {
            if block_by != n2 {
                self.blocks(block_by, n2, edge.reason);
            }
        }
        let n2 = self.get_node_mut(n2);
        // n2.contained_by.extend(to_merge.contained_by);
        n2.regions.extend(to_merge.regions);
    }
    fn kill_node(&mut self, n: NodeId) {
        let removed = self.remove_node(n);
        for (blocked_by, _) in removed.blocked_by {
            self.kill_node(blocked_by);
        }
    }
    fn remove_node(&mut self, n: NodeId) -> Node<'tcx> {
        let to_remove = self.nodes[n].take().unwrap();
        for &block in to_remove.blocks.keys() {
            let rem = self.get_node_mut(block).blocked_by.remove(&n);
            assert!(rem.is_some());
        }
        for &block_by in to_remove.blocked_by.keys() {
            let rem = self.get_node_mut(block_by).blocks.remove(&n);
            assert!(rem.is_some());
        }
        to_remove
    }
    pub(crate) fn get_node(&self, n: NodeId) -> &Node<'tcx> {
        self.nodes[n].as_ref().unwrap()
    }
    fn get_node_mut(&mut self, n: NodeId) -> &mut Node<'tcx> {
        self.nodes[n].as_mut().unwrap()
    }
    fn blocks(&mut self, n1: NodeId, n2: NodeId, reason: ConstraintCategory<'tcx>) {
        let block = Edge::new(n1, n2, reason);
        self.get_node_mut(n1).blocks.insert(n2, block);
        let blocked_by = Edge::new(n2, n1, reason);
        self.get_node_mut(n2).blocked_by.insert(n1, blocked_by);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Node<'tcx> {
    pub id: NodeId,
    pub regions: FxHashSet<RegionVid>,
    pub blocks: FxHashMap<NodeId, Edge<'tcx>>,
    pub blocked_by: FxHashMap<NodeId, Edge<'tcx>>,
    // pub contained_by: Vec<Local>,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Edge<'tcx> {
    pub from: NodeId,
    pub to: NodeId,
    pub reason: ConstraintCategory<'tcx>,
}

impl<'tcx> Edge<'tcx> {
    fn new(from: NodeId, to: NodeId, reason: ConstraintCategory<'tcx>) -> Self {
        Self { from, to, reason }
    }
}

impl<'tcx> Node<'tcx> {
    pub fn new(id: NodeId, r: RegionVid) -> Self {
        Self {
            id,
            regions: [r].into_iter().collect(),
            blocks: FxHashMap::default(),
            blocked_by: FxHashMap::default(),
            // contained_by: Vec::new(),
        }
    }
}

#[derive(Clone)]
pub struct Cg<'a, 'tcx> {
    pub(crate) repacker: PlaceRepacker<'a, 'tcx>,
    // pub(crate) facts: &'a BorrowckFacts,
    pub(crate) live: BitSet<BorrowIndex>,
    pub(crate) regions: Regions<'a, 'tcx>,
    pub done: usize,
}
impl<'a, 'tcx> Cg<'a, 'tcx> {
    pub(crate) fn new(repacker: PlaceRepacker<'a, 'tcx>, facts: &'a BorrowckFacts, facts2: &'a BorrowckFacts2<'tcx>) -> Self {
        let live = BitSet::new_empty(facts2.borrow_set.location_map.len() * 2);
        let regions = Regions {
            borrows: FxHashMap::default(),
            subset: Vec::new(),
            graph: Graph::new(repacker, facts, facts2),
        };
        Cg { repacker, live, regions, done: 0 }
    }
}

impl PartialEq for Cg<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        true
    }
}
impl Eq for Cg<'_, '_> {}

impl<'a, 'tcx> Debug for Cg<'a, 'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        // self.summary.fmt(f)
        Ok(())
    }
}
impl<'a, 'tcx> DebugWithContext<CoupligGraph<'a, 'tcx>> for Cg<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        _ctxt: &CoupligGraph<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        Ok(())
    }
}
