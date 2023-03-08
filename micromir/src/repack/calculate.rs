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
    check::checker, FreeState, MicroBasicBlockData, MicroBasicBlocks, MicroBody, MicroStatement,
    MicroTerminator, PermissionKind, TerminatorPlaceCapabilitySummary,
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
            // TODO: figure out if `always_live` should start as `Uninit` or `Exclusive`
            } else if local <= last_arg || always_live.contains(local) {
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
        let rp = PlaceRepacker::new(&self.body, tcx);
        let start_node = self.body.basic_blocks.start_node();

        // Do the actual repacking calculation
        self.basic_blocks
            .calculate_repacking(start_node, state, |bb| &preds[bb], rp);

        if cfg!(debug_assertions) {
            // println!("--------\n{}\n--------", &self.basic_blocks);
            checker::check(&self.basic_blocks, rp);
        }
    }
}

#[derive(Debug)]
struct Queue {
    queue: Vec<BasicBlock>,
    dirty_queue: FxHashSet<BasicBlock>,
    done: IndexVec<BasicBlock, bool>,
    can_redo: IndexVec<BasicBlock, bool>,
    recompute_count: IndexVec<BasicBlock, u32>,
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
            recompute_count: IndexVec::from_elem_n(0, len),
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
    #[tracing::instrument(name = "Queue::pop", level = "warn", skip(min_by), ret)]
    fn pop(&mut self, min_by: impl Fn(&BasicBlock) -> usize) -> Option<BasicBlock> {
        if let Some(bb) = self.queue.pop() {
            self.done[bb] = true;
            Some(bb)
        } else {
            if self.dirty_queue.is_empty() {
                debug_assert!((0..self.done.len())
                    .map(BasicBlock::from_usize)
                    .all(|bb| self.done[bb] || !self.can_redo[bb]));
                return None;
            }
            let bb = self
                .dirty_queue
                .iter()
                .copied()
                .filter(|bb| self.can_redo[*bb])
                .min_by_key(min_by)
                .unwrap(); // Can this happen? If so probably a bug
            self.can_redo[bb] = false;
            self.dirty_queue.remove(&bb);
            self.recompute_count[bb] += 1;
            // TODO: assert that recompute count is low
            assert!(self.recompute_count[bb] < 200);
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
        while let Some(can_do) = queue.pop(|bb: &BasicBlock| {
            let preds = preds(*bb);
            preds.len() - self.get_valid_pred_count(preds)
        }) {
            // if can_do.as_u32() == 27 {
            //     tracing::warn!("IJOFD");
            // }
            let is_cleanup = self.basic_blocks[can_do].is_cleanup;
            let predecessors = self.get_pred_pcs(preds(can_do));
            let initial = if predecessors.len() == 1 {
                predecessors[0].state().clone()
            } else {
                Self::calculate_join(can_do, predecessors, is_cleanup, rp)
            };
            // TODO: A better way to do this might be to calculate a pre/post for entire basic blocks;
            // start with pre/post of all `None` and walk over the statements collecting all the
            // pre/posts, ignoring some (e.g. if we already have `x.f` in our pre then if we ran into
            // `x.f.g` we'd ignore it, and if we ran into `x` we'd add `rp.expand(`x`, `x.f`).1`).
            // And then calculate the fixpoint from that (rather than having to go through all the
            // statements again each time). Then, once we have the state for the start and end of each
            // bb, we simply calculate intermediate states along with repacking for all straight-line
            // code within each bb.
            let changed = self.basic_blocks[can_do].calculate_repacking(initial, rp);
            if changed {
                queue.add_succs(&self.basic_blocks[can_do].terminator, &preds);
            }
        }
    }

    fn get_pred_pcs(
        &mut self,
        predecessors: &[BasicBlock],
    ) -> Vec<&mut TerminatorPlaceCapabilitySummary<'tcx>> {
        let predecessors = self
            .basic_blocks
            .iter_enumerated_mut()
            .filter(|(bb, _)| predecessors.contains(bb));
        predecessors
            .filter_map(|(_, bb)| bb.get_end_pcs_mut())
            .collect::<Vec<_>>()
    }

    fn get_valid_pred_count(&self, predecessors: &[BasicBlock]) -> usize {
        predecessors
            .iter()
            .map(|bb| &self.basic_blocks[*bb])
            .filter(|bb| bb.terminator.repack_join.is_some())
            .count()
    }

    #[tracing::instrument(level = "info", skip(rp))]
    fn calculate_join(
        bb: BasicBlock,
        predecessors: Vec<&mut TerminatorPlaceCapabilitySummary<'tcx>>,
        is_cleanup: bool,
        rp: PlaceRepacker<'_, 'tcx>,
    ) -> FreeState<'tcx> {
        let mut join = predecessors[0].state().clone();
        for pred in predecessors.iter().skip(1) {
            pred.state().join(&mut join, is_cleanup, rp);
            if cfg!(debug_assertions) {
                join.consistency_check(rp);
            }
        }
        for pred in predecessors {
            pred.join(&join, bb, is_cleanup, rp);
        }
        join
    }
}

impl<'tcx> MicroBasicBlockData<'tcx> {
    #[tracing::instrument(level = "info", skip(rp))]
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
        if cfg!(debug_assertions) {
            pre.consistency_check(rp);
        }
        self.repack_operands = Some(pcs);
        update.update_free(&mut pre);
        if cfg!(debug_assertions) {
            pre.consistency_check(rp);
        }
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
        if cfg!(debug_assertions) {
            pre.consistency_check(rp);
        }
        self.repack_operands = Some(pcs);
        update.update_free(&mut pre);
        if cfg!(debug_assertions) {
            pre.consistency_check(rp);
        }
        if let Some(pcs) = self.repack_join.as_mut() {
            let changed = pcs.state() != &pre;
            debug_assert!(!(changed && self.previous_rjs.contains(&pre)));
            if cfg!(debug_assertions) {
                let old = std::mem::replace(pcs.state_mut(), pre);
                self.previous_rjs.push(old);
            } else {
                *pcs.state_mut() = pre;
            }
            changed
        } else {
            self.repack_join = Some(TerminatorPlaceCapabilitySummary::empty(pre));
            true
        }
    }
}
