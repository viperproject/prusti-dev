// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    data_structures::{fx::FxHashSet, graph::WithStartNode},
    dataflow::storage,
    index::vec::{Idx, IndexVec},
    middle::{
        mir::{BasicBlock, HasLocalDecls, Local, RETURN_PLACE},
        ty::TyCtxt,
    },
};

use crate::{
    FreeState, MicroBasicBlockData, MicroBasicBlocks, MicroBody, MicroStatement, MicroTerminator,
    PermissionKind, PlaceCapabilitySummary,
};

use super::{place::PlaceRepacker, triple::ModifiesFreeState};

impl<'tcx> MicroBody<'tcx> {
    fn initial_free_state(&self) -> FreeState<'tcx> {
        let always_live = storage::always_storage_live_locals(&self.body);
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(self.body.arg_count);
        FreeState::initial(self.body.local_decls().len(), |local: Local| {
            if local == return_local {
                Some(PermissionKind::Uninit)
            } else if always_live.contains(local) {
                Some(PermissionKind::Exclusive)
            } else if local <= last_arg {
                Some(PermissionKind::Exclusive)
            } else {
                None
            }
        })
    }
    pub fn calculate_repacking(&mut self, tcx: TyCtxt<'tcx>) {
        // Safety check
        assert!(!self.done_repacking);
        self.done_repacking = true;

        // Calculate initial state
        let state = self.initial_free_state();
        let preds = self.body.basic_blocks.predecessors();
        let rp = PlaceRepacker::new(&*self.body, tcx);
        let start_node = self.body.basic_blocks.start_node();

        // Do the actual repacking calculation
        self.basic_blocks
            .calculate_repacking(start_node, state, |bb| &preds[bb], rp);
    }
}

#[derive(Debug)]
struct Queue {
    queue: Vec<BasicBlock>,
    dirty_queue: FxHashSet<BasicBlock>,
    done: IndexVec<BasicBlock, bool>,
    can_redo: IndexVec<BasicBlock, bool>,
}
impl Queue {
    fn new(start_node: BasicBlock, len: usize) -> Self {
        let mut done = IndexVec::from_elem_n(false, len);
        done[start_node] = true;
        Self {
            queue: Vec::new(),
            dirty_queue: FxHashSet::default(),
            done,
            can_redo: IndexVec::from_elem_n(true, len),
        }
    }
    fn add_succs<'a>(
        &mut self,
        term: &MicroTerminator,
        preds: impl Fn(BasicBlock) -> &'a [BasicBlock],
    ) {
        for succ in term.original_kind.successors() {
            if preds(succ).iter().all(|pred| self.done[*pred]) {
                debug_assert!(!self.done[succ]);
                self.queue.push(succ);
            } else {
                self.can_redo[succ] = true;
                self.dirty_queue.insert(succ);
            }
        }
    }
    #[tracing::instrument(name = "Queue::pop", level = "debug", ret)]
    fn pop(&mut self) -> Option<BasicBlock> {
        if let Some(bb) = self.queue.pop() {
            self.done[bb] = true;
            Some(bb)
        } else {
            if self.dirty_queue.len() == 0 {
                debug_assert!((0..self.done.len())
                    .into_iter()
                    .map(BasicBlock::from_usize)
                    .all(|bb| self.done[bb] || !self.can_redo[bb]));
                return None;
            }
            let bb = *self
                .dirty_queue
                .iter()
                .filter(|bb| self.can_redo[**bb])
                .next()
                .unwrap(); // Can this happen? If so probably a bug
            self.can_redo[bb] = false;
            self.dirty_queue.remove(&bb);
            Some(bb)
        }
    }
}

impl<'tcx> MicroBasicBlocks<'tcx> {
    pub(crate) fn calculate_repacking<'a>(
        &mut self,
        start_node: BasicBlock,
        initial: FreeState<'tcx>,
        preds: impl Fn(BasicBlock) -> &'a [BasicBlock],
        rp: PlaceRepacker<'_, 'tcx>,
    ) {
        debug_assert!(self
            .basic_blocks
            .indices()
            .all(|bb| bb == start_node || !preds(bb).is_empty()));

        self.basic_blocks[start_node].calculate_repacking(initial, rp);
        let mut queue = Queue::new(start_node, self.basic_blocks.len());
        queue.add_succs(&self.basic_blocks[start_node].terminator, &preds);
        while let Some(can_do) = queue.pop() {
            let is_cleanup = self.basic_blocks[can_do].is_cleanup;
            let predecessors = self.get_pred_pcs(preds(can_do));
            let initial = Self::calculate_join(predecessors, is_cleanup, rp);
            let changed = self.basic_blocks[can_do].calculate_repacking(initial, rp);
            if changed {
                queue.add_succs(&self.basic_blocks[can_do].terminator, &preds);
            }
        }
        // debug_assert!(done.iter().all(|b| *b), "{done:?}");
    }

    fn get_pred_pcs(
        &mut self,
        predecessors: &[BasicBlock],
    ) -> Vec<&mut PlaceCapabilitySummary<'tcx>> {
        let predecessors = self
            .basic_blocks
            .iter_enumerated_mut()
            .filter(|(bb, _)| predecessors.contains(bb));
        predecessors
            .filter_map(|(_, bb)| bb.get_pcs_mut())
            .collect::<Vec<_>>()
    }

    fn calculate_join(
        predecessors: Vec<&mut PlaceCapabilitySummary<'tcx>>,
        is_cleanup: bool,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> FreeState<'tcx> {
        let mut join = predecessors[0].state().clone();
        for pred in predecessors.iter().skip(1) {
            pred.state().join(&mut join, is_cleanup, rp);
        }
        // TODO: calculate the repacking statements needed
        // println!("join {join:#?} of\n{predecessors:#?}");
        join
    }
}

impl<'tcx> MicroBasicBlockData<'tcx> {
    pub(crate) fn calculate_repacking(
        &mut self,
        mut incoming: FreeState<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        // Check that we haven't already calculated this
        let pre_pcs = self
            .statements
            .first()
            .map(|stmt| &stmt.repack_operands)
            .unwrap_or_else(|| &self.terminator.repack_operands);
        if pre_pcs
            .as_ref()
            .map(|pcs| pcs.state() == &incoming)
            .unwrap_or_default()
        {
            return false;
        }
        // Do calculation for statements
        for stmt in &mut self.statements {
            incoming = stmt.calculate_repacking(incoming, rp);
        }
        // Do calculation for terminator
        self.terminator.calculate_repacking(incoming, rp)
    }
}

impl<'tcx> MicroStatement<'tcx> {
    #[tracing::instrument(level = "debug", skip(rp))]
    pub(crate) fn calculate_repacking(
        &mut self,
        incoming: FreeState<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> FreeState<'tcx> {
        let update = self.get_update(incoming.len());
        let (pcs, mut pre) = incoming.bridge(&update, rp);
        self.repack_operands = Some(pcs);
        update.update_free(&mut pre);
        pre
    }
}

impl<'tcx> MicroTerminator<'tcx> {
    #[tracing::instrument(level = "debug", skip(rp))]
    pub(crate) fn calculate_repacking(
        &mut self,
        incoming: FreeState<'tcx>,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> bool {
        let update = self.get_update(incoming.len());
        let (pcs, mut pre) = incoming.bridge(&update, rp);
        self.repack_operands = Some(pcs);
        update.update_free(&mut pre);
        let changed = self
            .repack_join
            .as_ref()
            .map(|pcs| pcs.state() != &pre)
            .unwrap_or(true);
        self.repack_join = Some(PlaceCapabilitySummary::empty(pre));
        changed
    }
}
