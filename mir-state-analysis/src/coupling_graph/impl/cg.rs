// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{fmt::{Debug, Formatter, Result, Display}, borrow::Cow};

use derive_more::{Deref, DerefMut};
use prusti_interface::environment::borrowck::facts::{BorrowckFacts, BorrowckFacts2};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    index::bit_set::BitSet,
    dataflow::fmt::DebugWithContext, index::IndexVec, middle::mir::Local,
    borrowck::{borrow_set::BorrowData, consumers::{BorrowIndex, OutlivesConstraint}},
    middle::{mir::{BasicBlock, ConstraintCategory, RETURN_PLACE, Location, Operand}, ty::{RegionVid, TyKind}},
};

use crate::{
    free_pcs::{
        engine::FreePlaceCapabilitySummary, CapabilityLocal, CapabilityProjections, RepackOp,
    },
    utils::{PlaceRepacker, Place},
};

use super::{engine::CoupligGraph, shared_borrow_set::SharedBorrowSet, CgContext, region_place::Perms};

#[derive(Clone)]
pub struct Graph<'a, 'tcx> {
    pub id: Option<String>,
    pub rp: PlaceRepacker<'a, 'tcx>,
    pub facts: &'a BorrowckFacts,
    pub facts2: &'a BorrowckFacts2<'tcx>,
    pub cgx: &'a CgContext<'a, 'tcx>,

    pub(crate) live: BitSet<BorrowIndex>,
    pub version: usize,
    pub skip_empty_nodes: bool,

    pub nodes: IndexVec<RegionVid, Node<'tcx>>,
    // Regions equal to 'static
    pub static_regions: FxHashSet<RegionVid>,
}

impl Debug for Graph<'_, '_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        f.debug_struct("Graph")
            .field("id", &self.id)
            .field("nodes", &self.nodes)
            .field("skip_empty_nodes", &self.skip_empty_nodes)
            // .field("static_regions", &self.static_regions)
            .finish()
    }
}

impl PartialEq for Graph<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.nodes == other.nodes //&& self.static_regions == other.static_regions
    }
}
impl Eq for Graph<'_, '_> {}

impl<'a, 'tcx: 'a> Graph<'a, 'tcx> {
    // TODO: get it from `UniversalRegions` instead
    pub fn static_region() -> RegionVid {
        RegionVid::from_u32(0)
    }
    pub fn new(rp: PlaceRepacker<'a, 'tcx>, facts: &'a BorrowckFacts, facts2: &'a BorrowckFacts2<'tcx>, cgx: &'a CgContext<'a, 'tcx>) -> Self {
        let live = BitSet::new_empty(facts2.borrow_set.location_map.len());
        let mut result = Self {
            id: None,
            rp,
            facts,
            facts2,
            cgx,
            live,
            version: 0,
            skip_empty_nodes: false,
            nodes: IndexVec::from_elem_n(Node::new(), facts2.region_inference_context.var_infos.len()),
            static_regions: FxHashSet::from_iter([Self::static_region()]),
        };
        // let input_facts = facts.input_facts.borrow();
        // for &(r1, r2) in &input_facts.as_ref().unwrap().known_placeholder_subset {
        //     result.outlives(r1, r2);
        // }

        ////// Ignore all global outlives constraints for now to have a nice graph (i.e. result is not in the same node as args)
        let input_facts = facts.input_facts.borrow();
        let input_facts = input_facts.as_ref().unwrap();
        let constraints: Vec<_> = facts2.region_inference_context.outlives_constraints().collect();
        let constraints_no_loc: Vec<_> = constraints.iter().filter(|c| c.locations.from_location().is_none()).copied().collect();

        // Make one single `'static` node
        // let n = result.region_to_node(Self::static_region());
        // let node = result.get_node_mut(n);
        // let mut to_make_static = vec![Self::static_region()];
        // while let Some(r) = to_make_static.pop() {
        //     for c in constraints.iter().filter(|c| c.sub == r) {
        //         if node.regions.insert(c.sup) {
        //             to_make_static.push(c.sup);
        //         }
        //     }
        // }
        // println!("Static node: {node:?}");
        // let mut to_make_static = vec![Self::static_region()];
        // while let Some(r) = to_make_static.pop() {
        //     for &c in constraints_no_loc.iter().filter(|c| c.sub == r) {
        //         if result.outlives(c) {
        //             to_make_static.push(c.sup);
        //         }
        //     }
        // }

        result
    }
    #[tracing::instrument(name = "Graph::outlives", level = "trace", skip(self), ret)]
    pub fn outlives(&mut self, c: OutlivesConstraint<'tcx>) -> bool {
        let edge = EdgeInfo {
            creation: c.locations.from_location().map(|l| l.block),
            reason: c.category,
        };
        self.outlives_inner(c.sup, c.sub, edge)
    }
    pub fn outlives_static(&mut self, r: RegionVid, l: Location) {
        let edge = EdgeInfo { creation: Some(l.block), reason: ConstraintCategory::Internal };
        self.outlives_inner(r, Self::static_region(), edge);
    }
    // sup outlives sub, or `sup: sub` (i.e. sup gets blocked)
    #[tracing::instrument(name = "Graph::outlives", level = "trace", skip(self), ret)]
    pub(crate) fn outlives_inner(&mut self, sup: RegionVid, sub: RegionVid, edge: EdgeInfo<'tcx>) -> bool {
        if sup == sub {
            panic!();
            return false;
        }
        if self.static_regions.contains(&sub) {
            Self::set_static_region(&self.nodes, &mut self.static_regions, sup);
        }
        self.nodes[sup].blocked_by.entry(sub).or_default().insert(edge);
        self.nodes[sub].blocks.entry(sup).or_default().insert(edge)
    }
    fn set_static_region(nodes: &IndexVec<RegionVid, Node<'tcx>>, static_regions: &mut FxHashSet<RegionVid>, r: RegionVid) {
        if static_regions.insert(r) {
            for &sup in nodes[r].blocks.keys() {
                Self::set_static_region(nodes, static_regions, sup);
            }
        }
    }

    #[tracing::instrument(name = "Graph::kill_borrow", level = "debug", skip(self))]
    /// Remove borrow from graph and all nodes that block it and the node it blocks
    pub fn kill_borrow(&mut self, data: &BorrowData<'tcx>) {
        if cfg!(debug_assertions) {
            let blocks = &self.nodes[data.region].blocks;
            assert_eq!(blocks.len(), 1);
            // A borrow should have places associated with it (i.e. be in the `region_map`)!
            assert_eq!(
                self.cgx.region_map[&data.region].place.local,
                self.cgx.region_map[blocks.keys().next().unwrap()].place.local
            );
        }
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
    pub fn remove(&mut self, r: RegionVid, l: Location) -> bool {
        let (blocks, blocked_by) = self.remove_all_edges(r);
        let changed = !(blocks.is_empty() && blocked_by.is_empty());
        for &block in blocks.keys() {
            for &blocked_by in blocked_by.keys() {
                // Do not rejoin nodes in a loop to themselves
                if blocked_by != block {
                    let edge = EdgeInfo { creation: Some(l.block), reason: ConstraintCategory::Internal };
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

    // #[tracing::instrument(name = "Graph::equate_regions", level = "trace", skip(self), ret)]
    // pub fn set_borrows_from_static(&mut self, r: RegionVid) -> bool {
    //     if let Some(n) = self.region_to_node(r) {
    //         self.set_borrows_from_static_node(n)
    //     } else {
    //         false
    //     }
    // }
    // fn set_borrows_from_static_node(&mut self, n: NodeId) -> bool {
    //     let node = self.get_node_mut(n);
    //     let already_set = node.borrows_from_static;
    //     node.borrows_from_static = true;
    //     already_set
    // }
    // #[tracing::instrument(name = "Graph::equate_regions", level = "trace", skip(self), ret)]
    // pub fn make_static(&mut self, r: RegionVid) -> bool {
    //     // TODO: instead of using `region_to_node`, do not add a node if already present?
    //     if let Some(n) = self.region_to_node(r) {
    //         self.make_static_node(n);
    //         true
    //     } else {
    //         false
    //     }
    // }
    // fn make_static_node(&mut self, n: NodeId) {
    //     // If there is a cycle we could have already removed and made static
    //     if let Some(mut node) = self.remove_node(n) {
    //         // println!("Making static node: {node:?}");
    //         // self.static_regions.extend(node.regions.drain());
    //         self.static_regions.insert(node.region);
    //         for (block_by, _) in node.blocked_by.drain() {
    //             // assert!(node.blocked_by.is_empty());
    //             self.set_borrows_from_static_node(block_by);
    //         }
    //         for (block, _) in node.blocks.drain() {
    //             self.make_static_node(block);
    //         }
    //     }
    // }

    // fn reachable(&self, from: NodeId, to: NodeId) -> Option<FxHashSet<NodeId>> {
    //     // println!("Checking reachability from {} to {}", from, to);
    //     let mut nodes = FxHashSet::default();
    //     if from == to {
    //         return Some(nodes);
    //     }
    //     for (&next, _) in &self.get_node(from).blocks {
    //         if let Some(others) = self.reachable(next, to) {
    //             nodes.insert(from);
    //             nodes.extend(others);
    //         }
    //     }
    //     if nodes.is_empty() {
    //         None
    //     } else {
    //         Some(nodes)
    //     }
    // }
    // fn region_to_node(&mut self, r: RegionVid) -> Option<NodeId> {
    //     if self.static_regions.contains(&r) {
    //         return None;
    //     }
    //     let mut last_none = self.nodes.len();
    //     for (i, n) in self.nodes.iter().enumerate() {
    //         if let Some(n) = n {
    //             // if n.regions.contains(&r) {
    //             if n.region == r {
    //                 return Some(i);
    //             }
    //         } else {
    //             last_none = i;
    //         }
    //     }
    //     if last_none == self.nodes.len() {
    //         self.nodes.push(Some(Node::new(last_none, r)));
    //     } else {
    //         self.nodes[last_none] = Some(Node::new(last_none, r));
    //     }
    //     Some(last_none)
    // }
    // fn kill_node(&mut self, n: NodeId) {
    //     let removed = self.remove_node(n).unwrap();
    //     for (blocked_by, _) in removed.blocked_by {
    //         // May have a diamond shape, so may
    //         if self.nodes[blocked_by].is_some() {
    //             self.kill_node(blocked_by);
    //         }
    //     }
    // }

    // fn remove_node_rejoin(&mut self, id: NodeId) -> Node<'tcx> {
    //     let n = self.remove_node(id).unwrap();
    //     for (&blocked_by, edge) in &n.blocked_by {
    //         for (&block, _) in &n.blocks {
    //             // Do not rejoin nodes in a loop to themselves
    //             if blocked_by != block {
    //                 self.blocks(blocked_by, block, edge);
    //             }
    //         }
    //         if n.borrows_from_static {
    //             self.set_borrows_from_static_node(blocked_by);
    //         }
    //     }
    //     n
    // }
    // // Remove node without rejoining the graph
    // fn remove_node(&mut self, n: NodeId) -> Option<Node<'tcx>> {
    //     let to_remove = self.nodes[n].take()?;
    //     for &block in to_remove.blocks.keys() {
    //         let rem = self.get_node_mut(block).blocked_by.remove(&n);
    //         assert!(rem.is_some());
    //     }
    //     for &block_by in to_remove.blocked_by.keys() {
    //         let rem = self.get_node_mut(block_by).blocks.remove(&n);
    //         assert!(rem.is_some());
    //     }
    //     Some(to_remove)
    // }
    // pub(crate) fn get_node(&self, n: NodeId) -> &Node<'tcx> {
    //     self.nodes[n].as_ref().unwrap()
    // }
    // fn get_node_mut(&mut self, n: NodeId) -> &mut Node<'tcx> {
    //     self.nodes[n].as_mut().unwrap()
    // }
    // fn blocks(&mut self, n1: NodeId, n2: NodeId, reason: &FxHashSet<EdgeInfo<'tcx>>) -> bool {
    //     assert_ne!(n1, n2);
    //     let mut changed = false;
    //     let reasons = self.get_node_mut(n1).blocks.entry(n2).or_default();
    //     let old_size = reasons.len();
    //     reasons.extend(reason);
    //     changed = changed || reasons.len() != old_size;
    //     let reasons = self.get_node_mut(n2).blocked_by.entry(n1).or_default();
    //     let old_size = reasons.len();
    //     reasons.extend(reason);
    //     changed = changed || reasons.len() != old_size;
    //     changed
    // }
    pub(crate) fn all_nodes(&self) -> impl Iterator<Item = (RegionVid, &Node<'tcx>)> {
        self.nodes.iter_enumerated().filter(|(_, n)| !n.blocked_by.is_empty() || !n.blocks.is_empty())
    }

    fn remove_all_edges(&mut self, r: RegionVid) -> (
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

    pub(crate) fn get_associated_place(&self, r: RegionVid) -> Option<&Perms<'tcx>> {
        self.cgx.region_map.get(&r)
    }
    pub(crate) fn has_associated_place(&self, r: RegionVid) -> bool {
        self.cgx.region_map.contains_key(&r)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node<'tcx> {
    // pub id: NodeId,
    // pub regions: FxHashSet<RegionVid>,
    // pub region: RegionVid,
    pub blocks: FxHashMap<RegionVid, FxHashSet<EdgeInfo<'tcx>>>,
    pub blocked_by: FxHashMap<RegionVid, FxHashSet<EdgeInfo<'tcx>>>,
    // pub borrows_from_static: bool,
    // pub contained_by: Vec<Local>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct EdgeInfo<'tcx> {
    pub creation: Option<BasicBlock>,
    pub reason: ConstraintCategory<'tcx>,
}

impl Display for EdgeInfo<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let reason = match self.reason {
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
            ConstraintCategory::Boring => "boring",
            ConstraintCategory::BoringNoLocation => "boring_nl",
            ConstraintCategory::Internal => "internal",
        };
        let creation = self.creation.map(|c| format!("{c:?}")).unwrap_or_else(|| "sig".to_string());
        write!(f, "{creation} ({reason})")
    }
}

impl<'tcx> Node<'tcx> {
    pub fn new() -> Self {
        Self {
            blocks: FxHashMap::default(),
            blocked_by: FxHashMap::default(),
            // contained_by: Vec::new(),
        }
    }
}

impl<'a, 'tcx> DebugWithContext<CoupligGraph<'a, 'tcx>> for Graph<'a, 'tcx> {
    fn fmt_diff_with(
        &self,
        old: &Self,
        _ctxt: &CoupligGraph<'a, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> Result {
        Ok(())
    }
}

impl<'tcx> Graph<'_, 'tcx> {
    #[tracing::instrument(name = "Regions::merge_for_return", level = "trace")]
    pub fn merge_for_return(&self) {
        let outlives: Vec<_> = self.facts2.region_inference_context.outlives_constraints().filter(|c| c.locations.from_location().is_none()).collect();
        let in_facts = self.facts.input_facts.borrow();
        let universal_region = &in_facts.as_ref().unwrap().universal_region;

        for (r, node) in self.all_nodes() {
            // Skip unknown empty nodes, we may want to figure out how to deal with them in the future
            if !self.has_associated_place(r) {
                continue;
            }

            if self.borrow_kind(r).is_some() {
                self.output_to_dot("log/coupling/error.dot");
                panic!("{node:?}");
            } else {
                // let r = *node.regions.iter().next().unwrap();
                if universal_region.contains(&r) {
                    continue;
                }

                let proof = outlives.iter().find(|c| {
                    universal_region.contains(&c.sub) && c.sup == r
                    // let r = c.sub.as_u32(); // The thing that lives shorter
                    // r == 0 || r == 1 // `0` means that it's static, `1` means that it's the function region
                });
                // If None then we have something left which doesn't outlive the function region!
                // if proof.is_none() {
                //     let in_facts = self.facts.input_facts.borrow();
                //     let r = &in_facts.as_ref().unwrap().universal_region;
                //     let outlives: Vec<_> = self.facts2.region_inference_context.outlives_constraints().collect();
                //     println!("Dumping graph to `log/coupling/error.dot`. Error: {outlives:?} (ur: {r:?})");
                //     // std::fs::remove_dir_all("log/coupling").ok();
                //     // std::fs::create_dir_all("log/coupling/individual").unwrap();
                //     let mut f = std::fs::File::create("log/coupling/error.dot").unwrap();
                //     dot::render(self, &mut f).unwrap();
                // }
                // println!("Found proof: {proof:?}");
                if proof.is_none() {
                    self.output_to_dot("log/coupling/error.dot");
                    panic!("Found a region which does not outlive the function region: {node:?} ({universal_region:?})");
                }
            }
        }
        for &r in &self.static_regions {
            if universal_region.contains(&r) {
                continue;
            }
            // It's possible that we get some random unnamed regions in the static set
            if !self.has_associated_place(r) {
                continue;
            }
            let proof = outlives.iter().find(|c| {
                universal_region.contains(&c.sub) && c.sup == r
            });
            if proof.is_none() {
                self.output_to_dot("log/coupling/error.dot");
                panic!("Found a region which does not outlive the function region: {r:?} ({universal_region:?})");
            }
        }
    }
    pub fn output_to_dot<P: AsRef<std::path::Path>>(&self, path: P) {
        // TODO:
        // return;
        let mut f = std::fs::File::create(path).unwrap();
        dot::render(self, &mut f).unwrap();
    }
}
