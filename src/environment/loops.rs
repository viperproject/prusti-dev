// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap, HashSet};
use rustc_data_structures::control_flow_graph::dominators::Dominators;
use rustc::mir;
use rustc::mir::visit::Visitor;
use environment::procedure::BasicBlockIndex;

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

#[derive(Clone, Debug)]
pub enum PlaceAccessKind {
    /// The place is assigned to.
    Store,
    /// The place is copied.
    Copy,
    /// The place is moved.
    Move,
    /// The place is borrowed immutably.
    SharedBorrow,
    /// The place is borrowed mutably.
    MutableBorrow,
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
        if self.body.contains(&location.block) {
            trace!("visit_place(place={:?}, context={:?}, location={:?})",
                   place, context, location);
            use rustc::mir::visit::PlaceContext::*;
            let access_kind = match context {
                Store => PlaceAccessKind::Store,
                Copy => PlaceAccessKind::Copy,
                Move => PlaceAccessKind::Move,
                Borrow { kind: mir::BorrowKind::Shared, .. } => PlaceAccessKind::SharedBorrow,
                Borrow { kind: mir::BorrowKind::Mut { .. }, .. } => PlaceAccessKind::MutableBorrow,
                _ => unimplemented!(),
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
    /// A map from loop heads to the corresponding bodies.
    pub loop_bodies: HashMap<BasicBlockIndex, HashSet<BasicBlockIndex>>,
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
        let loop_heads: Vec<_> = loop_bodies.keys().map(|k| *k).collect();
        ProcedureLoops {
            loop_heads: loop_heads,
            loop_bodies: loop_bodies,
            dominators: dominators,
        }
    }

    /// Compute what paths that come from the outside of the loop are accessed
    /// inside the loop.
    pub fn compute_used_paths<'a, 'tcx: 'a>(&self, loop_head: BasicBlockIndex,
                                            mir: &'a mir::Mir<'tcx>) -> Vec<PlaceAccess<'tcx>> {
        let body = self.loop_bodies.get(&loop_head).unwrap();
        let mut visitor = AccessCollector {
            body: body,
            accessed_places: Vec::new(),
        };
        visitor.visit_mir(mir);
        visitor.accessed_places
    }
}
