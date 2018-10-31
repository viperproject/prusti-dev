// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap, HashSet};
use rustc_data_structures::control_flow_graph::dominators::Dominators;
use rustc::mir;
use rustc::mir::visit::Visitor;
use environment::procedure::BasicBlockIndex;
use environment::place_set::PlaceSet;
use crate::utils;

/// A visitor that collects the loop heads and bodies.
struct LoopHeadCollector<'d> {
    /// Back edges (a, b) where b is a loop head.
    pub back_edges: Vec<(BasicBlockIndex, BasicBlockIndex)>,
    pub dominators: &'d Dominators<BasicBlockIndex>,
}

impl<'d, 'tcx> Visitor<'tcx> for LoopHeadCollector<'d> {

    fn visit_terminator_kind(
        &mut self,
        block: BasicBlockIndex,
        kind: &mir::TerminatorKind<'tcx>,
        _: mir::Location) {
        for successor in kind.successors() {
            if self.dominators.is_dominated_by(block, *successor) {
                self.back_edges.push((block, *successor));
                debug!("Loop head: {:?}", successor);
            }
        }
    }

}

/// A visitor for loopless code that visits a basic block only after all
/// predecessors of that basic block were already visited.
/// TODO: Either remove this trait or move it to a proper location.
trait PredecessorsFirstVisitor<'tcx>: Visitor<'tcx> {

    /// Should the given basic block be ignored?
    fn is_ignored(&mut self, bb: BasicBlockIndex) -> bool;

    fn visit_mir_from(&mut self, mir: &mir::Mir<'tcx>, start_block: BasicBlockIndex) {
        let mut work_queue = vec![start_block];
        let mut analysed_blocks = HashSet::new();
        while !work_queue.is_empty() {
            let current = work_queue.pop().unwrap();
            let basic_block_data = &mir.basic_blocks()[current];
            self.visit_basic_block_data(current, basic_block_data);
            analysed_blocks.insert(current);
            for &successor in basic_block_data.terminator().successors() {
                let mut all_predecessors_analysed = mir
                    .predecessors_for(successor)
                    .iter()
                    .all(|predecessor| {
                        analysed_blocks.contains(predecessor) ||
                        self.is_ignored(*predecessor)
                    });
                if all_predecessors_analysed {
                    assert!(!analysed_blocks.contains(&successor));
                    work_queue.push(successor);
                }
            }
        }
    }

}

/// Walk up the CFG graph an collect all basic blocks that belong to the loop body.
fn collect_loop_body<'tcx>(head: BasicBlockIndex, back_edge_source: BasicBlockIndex,
                           mir: &mir::Mir<'tcx>, body: &mut HashSet<BasicBlockIndex>) {
    let mut work_queue = vec![back_edge_source];
    body.insert(back_edge_source);
    while !work_queue.is_empty() {
        let current = work_queue.pop().unwrap();
        for &predecessor in mir.predecessors_for(current).iter() {
            if body.contains(&predecessor) {
                continue;
            }
            body.insert(predecessor);
            if predecessor != head {
                work_queue.push(predecessor);
            }
        }
    }
    debug!("Loop body (head={:?}): {:?}", head, body);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlaceAccessKind {
    /// The place is assigned to.
    Store,
    /// The place is read.
    Read,
    /// The place is moved (destructive read).
    Move,
    /// The place is borrowed immutably.
    SharedBorrow,
    /// The place is borrowed mutably.
    MutableBorrow,
}

impl PlaceAccessKind {

    /// Does the access require write permission to the leaf of the path?
    pub fn is_write_access(&self) -> bool {
        match &self {
            PlaceAccessKind::Store |
            PlaceAccessKind::Move |
            PlaceAccessKind::MutableBorrow => true,
            PlaceAccessKind::Read |
            PlaceAccessKind::SharedBorrow => false,
        }
    }
}

/// A place access inside a loop.
#[derive(Clone, Debug)]
pub struct PlaceAccess<'tcx> {
    pub location: mir::Location,
    pub place: mir::Place<'tcx>,
    pub kind: PlaceAccessKind,
}

/// A visitor that collects places that are defined before the loop and
/// accessed inside a loop.
///
/// Note that it is not guaranteed that `accessed_places` and
/// `defined_places` are disjoint
struct AccessCollector<'b, 'tcx> {
    /// Loop body.
    pub body: &'b HashSet<BasicBlockIndex>,
    /// The places that are defined before the loop and accessed inside a loop.
    pub accessed_places: Vec<PlaceAccess<'tcx>>,
}

impl<'b, 'tcx> Visitor<'tcx> for AccessCollector<'b, 'tcx> {

    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: mir::visit::PlaceContext<'tcx>,
        location: mir::Location
    ) {
        // TODO: using `location`, skip the places that are used for typechecking
        // because that part of the generated code contains closures.
        if self.body.contains(&location.block) {
            trace!("visit_place(place={:?}, context={:?}, location={:?})",
                   place, context, location);
            use rustc::mir::visit::PlaceContext::*;
            let access_kind = match context {
                Store => PlaceAccessKind::Store,
                Copy => PlaceAccessKind::Read,
                Move => PlaceAccessKind::Move,
                Borrow { kind: mir::BorrowKind::Shared, .. } => PlaceAccessKind::SharedBorrow,
                Borrow { kind: mir::BorrowKind::Mut { .. }, .. } => PlaceAccessKind::MutableBorrow,
                Call => PlaceAccessKind::Read,
                Inspect => PlaceAccessKind::Read,
                x => unimplemented!("{:?}", x),
            };
            let access = PlaceAccess {
                location: location,
                place: place.clone(),
                kind: access_kind,
            };
            self.accessed_places.push(access);
        }
    }

}


/// Struct that contains information about all loops in the procedure.
pub struct ProcedureLoops {
    /// A list of basic blocks that are loop heads.
    pub loop_heads: Vec<BasicBlockIndex>,
    /// The depth of each loop head, starting from one for a simple single loop.
    pub loop_head_depths: HashMap<BasicBlockIndex, usize>,
    /// A map from loop heads to the corresponding bodies.
    pub loop_bodies: HashMap<BasicBlockIndex, HashSet<BasicBlockIndex>>,
    /// A map from loop bodies to the ordered vector of enclosing loop heads.
    enclosing_loop_heads: HashMap<BasicBlockIndex, Vec<BasicBlockIndex>>,
    /// Back edges.
    pub back_edges: Vec<(BasicBlockIndex, BasicBlockIndex)>,
    /// Dominators graph.
    dominators: Dominators<BasicBlockIndex>,
}

impl ProcedureLoops {

    pub fn new<'a, 'tcx: 'a>(mir: &'a mir::Mir<'tcx>) -> ProcedureLoops {
        let dominators = mir.dominators();
        let back_edges;
        {
            let mut visitor = LoopHeadCollector {
                back_edges: Vec::new(),
                dominators: &dominators,
            };
            visitor.visit_mir(mir);
            back_edges = visitor.back_edges;
        }

        let mut loop_bodies = HashMap::new();
        for &(source, target) in back_edges.iter() {
            let body = loop_bodies.entry(target).or_insert(HashSet::new());
            collect_loop_body(target, source, mir, body);
        }

        let mut enclosing_loop_heads_set: HashMap<BasicBlockIndex, HashSet<BasicBlockIndex>> = HashMap::new();
        for (&loop_head, loop_body) in loop_bodies.iter() {
            for &block in loop_body.iter() {
                let heads_set = enclosing_loop_heads_set.entry(block).or_insert(HashSet::new());
                heads_set.insert(loop_head);
            }
        }

        let loop_heads: Vec<_> = loop_bodies.keys().map(|k| *k).collect();
        let mut loop_head_depths = HashMap::new();
        for &loop_head in loop_heads.iter() {
            loop_head_depths.insert(loop_head, enclosing_loop_heads_set[&loop_head].len());
        }

        let mut enclosing_loop_heads = HashMap::new();
        for (&block, loop_heads) in enclosing_loop_heads_set.iter() {
            let mut heads: Vec<BasicBlockIndex> = loop_heads.iter().cloned().collect();
            heads.sort_unstable_by_key(|bbi| loop_head_depths[bbi]);
            enclosing_loop_heads.insert(block, heads);
        }

        ProcedureLoops {
            loop_heads,
            loop_head_depths,
            loop_bodies,
            enclosing_loop_heads,
            back_edges: back_edges,
            dominators: dominators,
        }
    }

    pub fn count_loop_heads(&self) -> usize {
        self.loop_heads.len()
    }

    pub fn max_loop_nesting(&self) -> usize {
        self.loop_head_depths.values().max().cloned().unwrap_or(0)
    }

    pub fn is_loop_head(&self, bbi: BasicBlockIndex) -> bool {
        self.loop_head_depths.contains_key(&bbi)
    }

    /// Get the loop head, if any
    /// Note: a loop head **is** loop head of itself
    pub fn get_loop_head(&self, bbi: BasicBlockIndex) -> Option<BasicBlockIndex> {
        self.enclosing_loop_heads
            .get(&bbi)
            .and_then(|heads| heads.last())
            .cloned()
    }

    /// Get the depth of a loop head, starting from one
    pub fn get_loop_head_depth(&self, bbi: BasicBlockIndex) -> usize {
        self.loop_head_depths[&bbi]
    }

    /// Compute what paths that come from the outside of the loop are accessed
    /// inside the loop.
    fn compute_used_paths<'a, 'tcx: 'a>(&self, loop_head: BasicBlockIndex,
                                        mir: &'a mir::Mir<'tcx>) -> Vec<PlaceAccess<'tcx>> {
        let body = self.loop_bodies.get(&loop_head).unwrap();
        let mut visitor = AccessCollector {
            body: body,
            accessed_places: Vec::new(),
        };
        visitor.visit_mir(mir);
        visitor.accessed_places
    }

    /// If `definitely_initalised_paths` is not `None`, returns only leaves that are
    /// definitely initialised.
    pub fn compute_read_and_write_leaves<'a, 'tcx: 'a>(
        &self,
        loop_head: BasicBlockIndex,
        mir: &'a mir::Mir<'tcx>,
        definitely_initalised_paths: Option<&PlaceSet>,
    ) -> (Vec<mir::Place<'tcx>>, Vec<mir::Place<'tcx>>) {
        // 1.  Let ``A1`` be a set of pairs ``(p, t)`` where ``p`` is a prefix
        //     accessed in the loop body and ``t`` is the type of access (read,
        //     destructive read, …).
        // 2.  Let ``A2`` be a subset of ``A1`` that contains only the prefixes
        //     whose roots are defined before the loop. (The root of the prefix
        //     ``x.f.g.h`` is ``x``.)
        // 3.  Let ``A3`` be a subset of ``A2`` without accesses that are subsumed
        //     by other accesses.
        // 4.  Let ``U`` be a set of prefixes that are unreachable at the loop
        //     head because they are either moved out or mutably borrowed.
        // 5.  For each access ``(p, t)`` in the set ``A3``:
        //
        //     1.  Add a read permission to the loop invariant to read the prefix
        //         up to the last element. If needed, unfold the corresponding
        //         predicates.
        //     2.  Add a permission to the last element based on what is required
        //         by the type of access. If ``p`` is a prefix of some prefixes in
        //         ``U``, then the invariant would contain corresponding predicate
        //         bodies without unreachable elements instead of predicates.

        // Paths accessed inside the loop body.
        let accesses = self.compute_used_paths(loop_head, mir);
        debug!("accesses = {:?}", accesses);
        let mut accesses_pairs: Vec<_> = accesses.iter()
            .map(|PlaceAccess {place, kind, .. }| (place, kind))
            .collect();
        debug!("accesses_pairs = {:?}", accesses_pairs);
        if let Some(paths) = definitely_initalised_paths {
            debug!("definitely_initalised_paths = {:?}", paths);
            accesses_pairs = accesses_pairs
                .into_iter()
                .filter(|(place, kind)| {
                    paths.iter().any(
                        |initialised_place|
                        // If the prefix is definitely initialised, then this place is a potential
                        // loop invariant.
                        utils::is_prefix(place, initialised_place) ||
                        // If the access is store, then we only need the path to exist, which is
                        // guaranteed if we have at least some of the leaves still initialised.
                        //
                        // Note that the Rust compiler is even more permissive as explained in this
                        // issue: https://github.com/rust-lang/rust/issues/21232.
                        (
                            **kind == PlaceAccessKind::Store &&
                            utils::is_prefix(initialised_place, place)
                        )
                    )
                })
                .collect();
        }
        debug!("accesses_pairs = {:?}", accesses_pairs);
        // Paths to whose leaves we need write permissions.
        let mut write_leaves: Vec<mir::Place> = Vec::new();
        for (i, (place, kind)) in accesses_pairs.iter().enumerate() {
            if kind.is_write_access() {
                let has_prefix = accesses_pairs
                    .iter()
                    .any(|(potential_prefix, kind)|
                        kind.is_write_access() &&
                            place != potential_prefix &&
                            utils::is_prefix(place, potential_prefix)
                    );
                if !has_prefix && !write_leaves.contains(place) {
                    write_leaves.push((*place).clone());
                }
            }
        }
        debug!("write_leaves = {:?}", write_leaves);
        // Paths to whose leaves we need read permissions.
        let mut read_leaves: Vec<mir::Place> = Vec::new();
        for (i, (place, kind)) in accesses_pairs.iter().enumerate() {
            if !kind.is_write_access() {
                let has_prefix = accesses_pairs
                    .iter()
                    .any(|(potential_prefix, kind)|
                        place != potential_prefix &&
                            utils::is_prefix(place, potential_prefix)
                    );
                if !has_prefix && !read_leaves.contains(place) && !write_leaves.contains(place) {
                    read_leaves.push((*place).clone());
                }
            }
        }
        debug!("read_leaves = {:?}", read_leaves);

        (write_leaves, read_leaves)
    }

    /// Check if ``block`` is inside a loop.
    pub fn is_block_in_loop(&self, loop_head: BasicBlockIndex,
                            block: BasicBlockIndex) -> bool {
        self.dominators.is_dominated_by(block, loop_head)
    }
}
