// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    environment::{mir_sets::PlaceSet, mir_utils::RealEdges, procedure::BasicBlockIndex},
    utils,
};
use log::{debug, trace};
use prusti_rustc_interface::{
    data_structures::graph::dominators::Dominators,
    index::{Idx, IndexVec},
    middle::{mir, mir::visit::Visitor},
};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Clone, Debug)]
pub enum LoopAnalysisError {
    /// The loop contains unsupported place contexts
    UnsupportedPlaceContext(mir::visit::PlaceContext, mir::Location),
}

/// Walk up the CFG graph an collect all basic blocks that belong to the loop body.
#[tracing::instrument(level = "debug", skip(real_edges, body))]
fn collect_loop_body(
    head: BasicBlockIndex,
    back_edge_source: BasicBlockIndex,
    real_edges: &RealEdges,
    body: &mut FxHashSet<BasicBlockIndex>,
) {
    let mut work_queue = vec![back_edge_source];
    body.insert(back_edge_source);
    while let Some(current) = work_queue.pop() {
        for &predecessor in real_edges.predecessors(current).iter() {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
    /// Does the access write to the path?
    fn is_write_access(&self) -> bool {
        match &self {
            PlaceAccessKind::Store | PlaceAccessKind::Move => true,
            PlaceAccessKind::Read
            | PlaceAccessKind::MutableBorrow
            | PlaceAccessKind::SharedBorrow => false,
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
#[derive(Debug)]
struct AccessCollector<'b, 'tcx> {
    /// Loop body.
    pub body: &'b FxHashSet<BasicBlockIndex>,
    /// The places that are defined before the loop and accessed inside a loop.
    pub accessed_places: Vec<PlaceAccess<'tcx>>,
    /// Errors raised while visiting the loop
    pub errors: Vec<LoopAnalysisError>,
}

impl<'b, 'tcx> Visitor<'tcx> for AccessCollector<'b, 'tcx> {
    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: mir::visit::PlaceContext,
        location: mir::Location,
    ) {
        // TODO: using `location`, skip the places that are used for typechecking
        // because that part of the generated code contains closures.
        if self.body.contains(&location.block) && context.is_use() {
            trace!(
                "visit_place(place={:?}, context={:?}, location={:?})",
                place,
                context,
                location
            );
            use prusti_rustc_interface::middle::mir::visit::PlaceContext::*;
            let access_kind = match context {
                MutatingUse(mir::visit::MutatingUseContext::Store) => PlaceAccessKind::Store,
                MutatingUse(mir::visit::MutatingUseContext::Call) => PlaceAccessKind::Store,
                MutatingUse(mir::visit::MutatingUseContext::Borrow) => {
                    PlaceAccessKind::MutableBorrow
                }
                MutatingUse(mir::visit::MutatingUseContext::Drop) => PlaceAccessKind::Move,
                NonMutatingUse(mir::visit::NonMutatingUseContext::Copy) => PlaceAccessKind::Read,
                NonMutatingUse(mir::visit::NonMutatingUseContext::Move) => PlaceAccessKind::Move,
                NonMutatingUse(mir::visit::NonMutatingUseContext::Inspect) => PlaceAccessKind::Read,
                NonMutatingUse(mir::visit::NonMutatingUseContext::PlaceMention) => {
                    PlaceAccessKind::Read
                }
                NonMutatingUse(mir::visit::NonMutatingUseContext::SharedBorrow) => {
                    PlaceAccessKind::SharedBorrow
                }
                _ => {
                    self.errors.push(LoopAnalysisError::UnsupportedPlaceContext(
                        context, location,
                    ));
                    return;
                }
            };
            let access = PlaceAccess {
                location,
                place: *place,
                kind: access_kind,
            };
            self.accessed_places.push(access);
        }
    }
}

/// Returns the list of basic blocks ordered in the topological order (ignoring back edges).
fn order_basic_blocks<'tcx>(
    mir: &mir::Body<'tcx>,
    real_edges: &RealEdges,
    back_edges: &FxHashSet<(BasicBlockIndex, BasicBlockIndex)>,
    loop_depth: &dyn Fn(BasicBlockIndex) -> usize,
) -> Vec<BasicBlockIndex> {
    let basic_blocks = &mir.basic_blocks;
    let mut sorted_blocks = Vec::new();
    let mut permanent_mark =
        IndexVec::<BasicBlockIndex, bool>::from_elem_n(false, basic_blocks.len());
    let mut temporary_mark = permanent_mark.clone();

    fn visit(
        real_edges: &RealEdges,
        back_edges: &FxHashSet<(BasicBlockIndex, BasicBlockIndex)>,
        loop_depth: &dyn Fn(BasicBlockIndex) -> usize,
        current: BasicBlockIndex,
        sorted_blocks: &mut Vec<BasicBlockIndex>,
        permanent_mark: &mut IndexVec<BasicBlockIndex, bool>,
        temporary_mark: &mut IndexVec<BasicBlockIndex, bool>,
    ) {
        if permanent_mark[current] {
            return;
        }
        assert!(!temporary_mark[current], "Not a DAG!");
        temporary_mark[current] = true;
        let curr_depth = loop_depth(current);
        // We want to order the loop body before exit edges
        let successors_groups: Vec<Vec<_>> = vec![
            real_edges
                .successors(current)
                .iter()
                .filter(|&&bb| loop_depth(bb) < curr_depth)
                .cloned()
                .collect(),
            real_edges
                .successors(current)
                .iter()
                .filter(|&&bb| loop_depth(bb) >= curr_depth)
                .cloned()
                .collect(),
        ];
        for group in &successors_groups {
            for &successor in group.iter() {
                if back_edges.contains(&(current, successor)) {
                    continue;
                }
                visit(
                    real_edges,
                    back_edges,
                    loop_depth,
                    successor,
                    sorted_blocks,
                    permanent_mark,
                    temporary_mark,
                );
            }
        }
        permanent_mark[current] = true;
        sorted_blocks.push(current);
    }

    while let Some(index) = permanent_mark.iter().position(|x| !*x) {
        let index = BasicBlockIndex::new(index);
        visit(
            real_edges,
            back_edges,
            loop_depth,
            index,
            &mut sorted_blocks,
            &mut permanent_mark,
            &mut temporary_mark,
        );
    }
    sorted_blocks.reverse();
    sorted_blocks
}

/// Struct that contains information about all loops in the procedure.
#[derive(Clone)]
pub struct ProcedureLoops {
    /// A list of basic blocks that are loop heads.
    pub loop_heads: FxHashSet<BasicBlockIndex>,
    /// The depth of each loop head, starting from one for a simple single loop.
    pub loop_head_depths: FxHashMap<BasicBlockIndex, usize>,
    /// A map from loop heads to the corresponding bodies.
    pub loop_bodies: FxHashMap<BasicBlockIndex, FxHashSet<BasicBlockIndex>>,
    pub ordered_loop_bodies: FxHashMap<BasicBlockIndex, Vec<BasicBlockIndex>>,
    /// A map from loop bodies to the ordered vector of enclosing loop heads (from outer to inner).
    enclosing_loop_heads: FxHashMap<BasicBlockIndex, Vec<BasicBlockIndex>>,
    /// A map from loop heads to the ordered blocks from which a CFG edge exits from the loop.
    loop_exit_blocks: FxHashMap<BasicBlockIndex, Vec<BasicBlockIndex>>,
    /// A map from loop heads to the nonconditional blocks (i.e. those that are always executed
    /// in any loop iteration).
    nonconditional_loop_blocks: FxHashMap<BasicBlockIndex, FxHashSet<BasicBlockIndex>>,
    /// Back edges.
    pub back_edges: FxHashSet<(BasicBlockIndex, BasicBlockIndex)>,
    /// Dominators graph.
    dominators: Dominators<BasicBlockIndex>,
    /// The list of basic blocks ordered in the topological order (ignoring back edges).
    pub ordered_blocks: Vec<BasicBlockIndex>,
}

pub type ReadAndWriteLeaves<'tcx> = (
    Vec<mir::Place<'tcx>>,
    Vec<mir::Place<'tcx>>,
    Vec<mir::Place<'tcx>>,
);

impl ProcedureLoops {
    #[tracing::instrument(name = "ProcedureLoops::new", level = "trace", skip(mir, real_edges))]
    pub fn new<'a, 'tcx: 'a>(mir: &'a mir::Body<'tcx>, real_edges: &RealEdges) -> ProcedureLoops {
        let dominators = mir.basic_blocks.dominators().clone();

        let mut back_edges: FxHashSet<(_, _)> = FxHashSet::default();
        for bb in mir.basic_blocks.indices() {
            for successor in real_edges.successors(bb) {
                if dominators.dominates(*successor, bb) {
                    back_edges.insert((bb, *successor));
                    debug!("Loop head: {:?}", successor);
                }
            }
        }

        let mut loop_bodies = FxHashMap::default();
        for &(source, target) in back_edges.iter() {
            let body = loop_bodies.entry(target).or_default();
            collect_loop_body(target, source, real_edges, body);
        }

        let mut enclosing_loop_heads_set: FxHashMap<BasicBlockIndex, FxHashSet<BasicBlockIndex>> =
            FxHashMap::default();
        for (&loop_head, loop_body) in loop_bodies.iter() {
            for &block in loop_body.iter() {
                let heads_set = enclosing_loop_heads_set.entry(block).or_default();
                heads_set.insert(loop_head);
            }
        }

        let loop_heads: FxHashSet<_> = loop_bodies.keys().copied().collect();
        let mut loop_head_depths = FxHashMap::default();
        for &loop_head in loop_heads.iter() {
            loop_head_depths.insert(loop_head, enclosing_loop_heads_set[&loop_head].len());
        }

        let mut enclosing_loop_heads = FxHashMap::default();
        for (&block, loop_heads) in enclosing_loop_heads_set.iter() {
            let mut heads: Vec<BasicBlockIndex> = loop_heads.iter().cloned().collect();
            heads.sort_unstable_by_key(|bbi| loop_head_depths[bbi]);
            enclosing_loop_heads.insert(block, heads);
        }

        let get_loop_depth = |bb: BasicBlockIndex| {
            enclosing_loop_heads
                .get(&bb)
                .and_then(|heads| heads.last())
                .map(|bb_head| loop_head_depths[bb_head])
                .unwrap_or(0)
        };

        let ordered_blocks = order_basic_blocks(mir, real_edges, &back_edges, &get_loop_depth);
        let block_order: FxHashMap<BasicBlockIndex, usize> = ordered_blocks
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, v)| (v, i))
            .collect();
        debug!("ordered_blocks: {:?}", ordered_blocks);

        let mut ordered_loop_bodies = FxHashMap::default();
        for (&loop_head, loop_body) in loop_bodies.iter() {
            let mut ordered_body: Vec<_> = loop_body.iter().cloned().collect();
            ordered_body.sort_unstable_by_key(|bb| block_order[bb]);
            debug_assert_eq!(loop_head, ordered_body[0]);
            ordered_loop_bodies.insert(loop_head, ordered_body);
        }

        // In Rust, the evaluation of a loop guard may happen over several blocks.
        // Here, we identify the CFG blocks that decide whether to exit from the loop or not.
        // They are those blocks in the loop that:
        // 1. have a SwitchInt terminator (TODO: can we remove this condition?)
        // 2. have an out-edge that exits from the loop
        let mut loop_exit_blocks = FxHashMap::default();
        for &loop_head in loop_heads.iter() {
            let loop_head_depth = loop_head_depths[&loop_head];
            let loop_body = &loop_bodies[&loop_head];
            let ordered_loop_body = &ordered_loop_bodies[&loop_head];

            let mut exit_blocks = vec![];
            let mut border = FxHashSet::default();
            border.insert(loop_head);

            for &curr_bb in ordered_loop_body {
                debug_assert!(border.contains(&curr_bb));

                // Decide if this block has an exit edge
                let term = mir[curr_bb].terminator();
                let is_switch_int = matches!(term.kind, mir::TerminatorKind::SwitchInt { .. });
                let has_exit_edge = real_edges
                    .successors(curr_bb)
                    .iter()
                    .any(|&bb| get_loop_depth(bb) < loop_head_depth);
                if is_switch_int && has_exit_edge {
                    exit_blocks.push(curr_bb);
                }

                border.remove(&curr_bb);

                for &succ_bb in real_edges.successors(curr_bb) {
                    if !back_edges.contains(&(curr_bb, succ_bb)) {
                        // Consider only forward in-loop edges
                        if loop_body.contains(&succ_bb) {
                            border.insert(succ_bb);
                        }
                    }
                }
            }

            loop_exit_blocks.insert(loop_head, exit_blocks);
        }
        debug!("loop_exit_blocks: {:?}", loop_exit_blocks);

        // The nonconditional blocks of a loop are those blocks of the loop body that dominate all
        // the blocks from which a back-edge starts.
        let mut nonconditional_loop_blocks = FxHashMap::default();
        for (&loop_head, loop_body) in loop_bodies.iter() {
            nonconditional_loop_blocks.insert(loop_head, loop_body.clone());
        }
        for &(back_edge_source, loop_head) in back_edges.iter() {
            let blocks = nonconditional_loop_blocks.get_mut(&loop_head).unwrap();
            *blocks = blocks
                .intersection(&dominators.dominators(back_edge_source).collect())
                .copied()
                .collect();
        }
        debug!(
            "nonconditional_loop_blocks: {:?}",
            nonconditional_loop_blocks
        );

        ProcedureLoops {
            loop_heads,
            loop_head_depths,
            loop_bodies,
            ordered_loop_bodies,
            enclosing_loop_heads,
            loop_exit_blocks,
            nonconditional_loop_blocks,
            back_edges,
            dominators,
            ordered_blocks,
        }
    }

    pub fn count_loop_heads(&self) -> usize {
        self.loop_heads.len()
    }

    pub fn max_loop_nesting(&self) -> usize {
        self.loop_head_depths.values().max().cloned().unwrap_or(0)
    }

    pub fn is_loop_head(&self, bbi: BasicBlockIndex) -> bool {
        self.loop_heads.contains(&bbi)
    }

    pub fn get_loop_exit_blocks(&self, bbi: BasicBlockIndex) -> &[BasicBlockIndex] {
        debug_assert!(self.is_loop_head(bbi));
        &self.loop_exit_blocks[&bbi]
    }

    pub fn is_conditional_branch(&self, loop_head: BasicBlockIndex, bbi: BasicBlockIndex) -> bool {
        debug_assert!(self.is_loop_head(loop_head));
        !self.nonconditional_loop_blocks[&loop_head].contains(&bbi)
    }

    pub fn get_enclosing_loop_heads(&self, bbi: BasicBlockIndex) -> &[BasicBlockIndex] {
        if let Some(heads) = self.enclosing_loop_heads.get(&bbi) {
            heads
        } else {
            &[]
        }
    }

    /// Get the loop head, if any
    /// Note: a loop head **is** loop head of itself
    pub fn get_loop_head(&self, bbi: BasicBlockIndex) -> Option<BasicBlockIndex> {
        self.enclosing_loop_heads
            .get(&bbi)
            .and_then(|heads| heads.last())
            .cloned()
    }

    /// Get the depth of a loop head, starting from one for a simple loop
    pub fn get_loop_head_depth(&self, bbi: BasicBlockIndex) -> usize {
        debug_assert!(self.is_loop_head(bbi));
        self.loop_head_depths[&bbi]
    }

    /// Get the loop-depth of a block (zero if it's not in a loop).
    pub fn get_loop_depth(&self, bbi: BasicBlockIndex) -> usize {
        self.get_loop_head(bbi)
            .map(|x| self.get_loop_head_depth(x))
            .unwrap_or(0)
    }

    /// Get the (topologically ordered) body of a loop, given a loop head
    pub fn get_loop_body(&self, loop_head: BasicBlockIndex) -> &[BasicBlockIndex] {
        debug_assert!(self.is_loop_head(loop_head));
        &self.ordered_loop_bodies[&loop_head]
    }

    /// Does this edge exit a loop?
    pub fn is_out_edge(&self, from: BasicBlockIndex, to: BasicBlockIndex) -> bool {
        if let Some(from_loop_head) = self.get_loop_head(from) {
            if let Some(to_loop_head) = self.get_loop_head(to) {
                if from_loop_head == to_loop_head || to == to_loop_head {
                    false
                } else {
                    !self.enclosing_loop_heads[&to].contains(&from_loop_head)
                }
            } else {
                true
            }
        } else {
            false
        }
    }

    /// Check if ``block`` is inside a given loop.
    pub fn is_block_in_loop(&self, loop_head: BasicBlockIndex, block: BasicBlockIndex) -> bool {
        self.dominators.dominates(loop_head, block)
    }

    /// Compute what paths that are accessed inside the loop.
    fn compute_used_paths<'a, 'tcx: 'a>(
        &self,
        loop_head: BasicBlockIndex,
        mir: &'a mir::Body<'tcx>,
    ) -> Result<Vec<PlaceAccess<'tcx>>, LoopAnalysisError> {
        let body = self.loop_bodies.get(&loop_head).unwrap();
        let mut visitor = AccessCollector {
            body,
            accessed_places: Vec::new(),
            errors: Vec::new(),
        };
        visitor.visit_body(mir);
        if let Some(error) = visitor.errors.into_iter().next() {
            Err(error)
        } else {
            Ok(visitor.accessed_places)
        }
    }

    /// If `definitely_initalised_paths` is not `None`, returns only leaves that are
    /// definitely initialised.
    #[tracing::instrument(level = "debug", skip(self, mir, definitely_initalised_paths))]
    pub fn compute_read_and_write_leaves<'a, 'tcx: 'a>(
        &self,
        loop_head: BasicBlockIndex,
        mir: &'a mir::Body<'tcx>,
        definitely_initalised_paths: Option<&PlaceSet<'tcx>>,
    ) -> Result<ReadAndWriteLeaves<'tcx>, LoopAnalysisError> {
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
        let accesses = self.compute_used_paths(loop_head, mir)?;
        debug!("accesses = {:?}", accesses);
        let mut accesses_pairs: Vec<_> = accesses
            .iter()
            .map(|PlaceAccess { place, kind, .. }| (*place, *kind))
            .collect();
        debug!("accesses_pairs = {:?}", accesses_pairs);
        if let Some(paths) = definitely_initalised_paths {
            debug!("definitely_initalised_paths = {:?}", paths);
            accesses_pairs.retain(|(place, kind)| {
                paths.iter().any(|initialised_place|
                        // If the prefix is definitely initialised, then this place is a potential
                        // loop invariant.
                        utils::is_prefix(*place, *initialised_place) ||
                        // If the access is store, then we only need the path to exist, which is
                        // guaranteed if we have at least some of the leaves still initialised.
                        //
                        // Note that the Rust compiler is even more permissive as explained in this
                        // issue: https://github.com/rust-lang/rust/issues/21232.
                        (
                            *kind == PlaceAccessKind::Store &&
                            utils::is_prefix(*initialised_place, *place)
                        ))
            });
        }
        debug!("accesses_pairs = {:?}", accesses_pairs);
        // Paths to whose leaves we need write permissions.
        let mut write_leaves: Vec<mir::Place> = Vec::new();
        for (place, kind) in accesses_pairs.iter() {
            if kind.is_write_access() {
                let has_prefix = accesses_pairs.iter().any(|(potential_prefix, kind)| {
                    kind.is_write_access()
                        && place != potential_prefix
                        && utils::is_prefix(*place, *potential_prefix)
                });
                if !has_prefix && !write_leaves.contains(place) {
                    write_leaves.push(*place);
                }
            }
        }
        debug!("write_leaves = {:?}", write_leaves);

        // Paths to whose leaves are roots of trees to which we need write permissions.
        let mut mut_borrow_leaves: Vec<mir::Place> = Vec::new();
        for (place, kind) in accesses_pairs.iter() {
            if *kind == PlaceAccessKind::MutableBorrow {
                let has_prefix = accesses_pairs.iter().any(|(potential_prefix, kind)| {
                    (kind.is_write_access() || *kind == PlaceAccessKind::MutableBorrow)
                        && place != potential_prefix
                        && utils::is_prefix(*place, *potential_prefix)
                });
                if !has_prefix
                    && !write_leaves.contains(place)
                    && !mut_borrow_leaves.contains(place)
                {
                    mut_borrow_leaves.push(*place);
                }
            }
        }
        debug!("mut_borrow_leaves = {:?}", write_leaves);

        // Paths to whose leaves we need read permissions.
        let mut read_leaves: Vec<mir::Place> = Vec::new();
        for (place, kind) in accesses_pairs.iter() {
            if !kind.is_write_access() {
                let has_prefix = accesses_pairs.iter().any(|(potential_prefix, _kind)| {
                    place != potential_prefix && utils::is_prefix(*place, *potential_prefix)
                });
                if !has_prefix
                    && !read_leaves.contains(place)
                    && !write_leaves.contains(place)
                    && !mut_borrow_leaves.contains(place)
                {
                    read_leaves.push(*place);
                }
            }
        }
        debug!("read_leaves = {:?}", read_leaves);

        Ok((write_leaves, mut_borrow_leaves, read_leaves))
    }
}
