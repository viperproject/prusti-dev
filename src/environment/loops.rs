// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap, HashSet};
use rustc_data_structures::control_flow_graph::dominators::Dominators;
use rustc::mir;
use rustc::mir::visit::Visitor;
use environment::procedure::{BasicBlockIndex, BasicBlockData, Procedure};

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
        for successor in kind.successors().iter() {
            if self.dominators.is_dominated_by(block, *successor) {
                self.back_edges.push((block, *successor));
                debug!("Loop head: {:?}", successor);
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
        let currect = work_queue.pop().unwrap();
        for &predecessor in mir.predecessors_for(currect).iter() {
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
pub struct PlaceAccess<'tcx> {
    pub location: mir::Location,
    pub place: mir::Place<'tcx>,
    pub kind: PlaceAccessKind,
}

/// A visitor that collects information about what paths are accessed
/// inside a loop.
struct AccessCollector<'b, 'tcx> {
    pub body: &'b HashSet<BasicBlockIndex>,
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
        let mut back_edges;
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
        let mut loop_heads: Vec<_> = loop_bodies.keys().map(|k| *k).collect();
        ProcedureLoops {
            loop_heads: loop_heads,
            loop_bodies: loop_bodies,
            dominators: dominators,
        }
    }

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
