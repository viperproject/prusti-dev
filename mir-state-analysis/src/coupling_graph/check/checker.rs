// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    ast::Mutability,
    borrowck::borrow_set::BorrowData,
    data_structures::fx::{FxHashMap, FxHashSet},
    index::IndexVec,
    middle::{
        mir::{visit::Visitor, BorrowKind, Location, ProjectionElem, Statement},
        ty::RegionVid,
    },
};

use crate::{
    coupling_graph::{
        coupling::{Block, CouplingOp},
        cursor::CgAnalysis,
        graph::Graph,
        region_info::map::RegionKind,
        CgContext,
    },
    free_pcs::{
        consistency::CapabilityConsistency, CapabilityKind, CapabilityLocal, CapabilitySummary,
        Fpcs, FpcsBound, FreePcsAnalysis, RepackOp,
    },
    utils::{Place, PlaceRepacker},
};

#[derive(Clone)]
struct CouplingState<'a, 'tcx> {
    blocks: IndexVec<RegionVid, FxHashSet<RegionVid>>,
    blocked_by: IndexVec<RegionVid, FxHashSet<RegionVid>>,
    waiting_to_activate: FxHashSet<RegionVid>,
    cgx: &'a CgContext<'a, 'tcx>,
}

impl<'a, 'tcx> std::fmt::Debug for CouplingState<'a, 'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.blocks.iter_enumerated())
            .finish()
    }
}

#[tracing::instrument(name = "cg::check", level = "debug", skip(cg, fpcs_cursor))]
pub(crate) fn check<'tcx>(
    mut cg: CgAnalysis<'_, '_, 'tcx>,
    mut fpcs_cursor: FreePcsAnalysis<'_, 'tcx>,
) {
    let cgx = cg.cgx();
    let rp: PlaceRepacker<'_, '_> = cgx.rp;
    let body = rp.body();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        cg.analysis_for_bb(block);
        fpcs_cursor.analysis_for_bb(block);

        let mut cg_state = CouplingState {
            blocks: IndexVec::from_elem_n(FxHashSet::default(), cgx.region_info.map.region_len()),
            blocked_by: IndexVec::from_elem_n(
                FxHashSet::default(),
                cgx.region_info.map.region_len(),
            ),
            waiting_to_activate: FxHashSet::default(),
            cgx,
        };
        cg_state.initialize(&cg.initial_state());
        assert!(cg_state.compare(&cg.initial_state())); // TODO: remove

        fpcs_cursor.set_bound_non_empty();
        let mut fpcs = Fpcs {
            summary: fpcs_cursor.initial_state().clone(),
            apply_pre_effect: false,
            bottom: false,
            repackings: Vec::new(),
            repacker: rp,
            bound: FpcsBound::empty(true),
        };
        // Consistency
        fpcs.summary.consistency_check(rp);
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let loc = Location {
                block,
                statement_index,
            };
            cg_state.check_location(loc, stmt, &mut fpcs, &mut cg, &mut fpcs_cursor);
        }
        let loc = Location {
            block,
            statement_index: data.statements.len(),
        };
        let cg_before = cg.before_next(loc);
        // Couplings
        for c in cg_before.couplings {
            c.update_free(&mut cg_state, false);
        }

        let bound: Box<dyn Fn(Place<'tcx>) -> CapabilityKind> =
            Box::new(cg_state.mk_capability_upper_bound());
        fpcs_cursor.set_bound(unsafe { std::mem::transmute(bound) });
        let fpcs_after = fpcs_cursor.next(loc);
        assert_eq!(fpcs_after.location, loc);
        fpcs_cursor.unset_bound();

        // Repacks
        for op in fpcs_after.repacks_middle {
            op.update_free(&mut fpcs.summary, false, rp);
        }
        // Couplings bound set
        let bound: Box<dyn Fn(Place<'tcx>) -> CapabilityKind> =
            Box::new(cg_state.mk_capability_upper_bound());
        fpcs.bound.borrow_mut().0 = Some(unsafe { std::mem::transmute(bound) });
        // Consistency
        fpcs.summary.consistency_check(rp);
        // Statement pre
        assert!(fpcs.repackings.is_empty());
        fpcs.apply_pre_effect = true;
        fpcs.visit_terminator(data.terminator(), loc);
        // Repacks
        for op in fpcs_after.repacks {
            op.update_free(&mut fpcs.summary, false, rp);
        }
        // Statement post
        assert!(fpcs.repackings.is_empty());
        fpcs.apply_pre_effect = false;
        fpcs.visit_terminator(data.terminator(), loc);
        assert!(fpcs.repackings.is_empty());
        // Consistency
        fpcs.summary.consistency_check(rp);
        // Couplings bound unset
        fpcs.bound.borrow_mut().0 = None;

        assert_eq!(fpcs.summary, fpcs_after.state);

        let cg_after = cg.next(loc);
        // Couplings
        for c in cg_after.couplings {
            c.update_free(&mut cg_state, false);
        }
        assert!(cg_state.compare(&cg_after.state), "{loc:?}");

        let fpcs_end = fpcs_cursor.terminator();
        let cg_end = cg.terminator();

        for (fpcs_succ, cg_succ) in fpcs_end.succs.into_iter().zip(cg_end.succs) {
            assert_eq!(fpcs_succ.location, cg_succ.location);
            // Repacks
            let mut fpcs_from = fpcs.clone();
            for op in fpcs_succ.repacks {
                op.update_free(
                    &mut fpcs_from.summary,
                    body.basic_blocks[fpcs_succ.location.block].is_cleanup,
                    rp,
                );
            }
            assert_eq!(fpcs_from.summary, fpcs_succ.state);

            // Couplings
            let mut cg_from = cg_state.clone();
            for op in cg_succ.couplings {
                op.update_free(&mut cg_from, false);
            }
            assert!(
                cg_from.compare(&cg_succ.state),
                "{loc:?} -> {:?}",
                cg_succ.location
            );
        }
    }
}

impl<'a, 'tcx> CouplingState<'a, 'tcx> {
    fn initialize(&mut self, graph: &Graph<'tcx>) {
        for (sub, v) in graph.nodes.iter_enumerated() {
            for sup in v.true_edges() {
                self.blocks[sub].insert(sup);
                self.blocked_by[sup].insert(sub);
            }
        }
        self.waiting_to_activate = graph.inactive_loans.clone();
    }

    #[tracing::instrument(
        name = "CouplingState::check_location",
        level = "trace",
        skip(self, stmt, cg, fpcs, fpcs_cursor)
    )]
    fn check_location(
        &mut self,
        loc: Location,
        stmt: &Statement<'tcx>,
        fpcs: &mut Fpcs<'_, 'tcx>,
        cg: &mut CgAnalysis<'_, '_, 'tcx>,
        fpcs_cursor: &mut FreePcsAnalysis<'_, 'tcx>,
    ) {
        let rp = self.cgx.rp;

        let cg_before = cg.before_next(loc);
        // Couplings
        for c in cg_before.couplings {
            c.update_free(self, false);
        }

        let bound: Box<dyn Fn(Place<'tcx>) -> CapabilityKind> =
            Box::new(self.mk_capability_upper_bound());
        fpcs_cursor.set_bound(unsafe { std::mem::transmute(bound) });
        let fpcs_after = fpcs_cursor.next(loc);
        assert_eq!(fpcs_after.location, loc);
        fpcs_cursor.unset_bound();

        // Repacks
        for op in fpcs_after.repacks_middle {
            op.update_free(&mut fpcs.summary, false, rp);
        }
        // Couplings bound set
        let bound: Box<dyn Fn(Place<'tcx>) -> CapabilityKind> =
            Box::new(self.mk_capability_upper_bound());
        fpcs.bound.borrow_mut().0 = Some(unsafe { std::mem::transmute(bound) }); // Extend lifetimes (safe since we unset it later)
                                                                                 // Consistency
        fpcs.summary.consistency_check(rp);
        // Statement pre
        assert!(fpcs.repackings.is_empty());
        fpcs.apply_pre_effect = true;
        fpcs.visit_statement(stmt, loc);
        assert!(fpcs.repackings.is_empty());
        // Repacks
        for op in fpcs_after.repacks {
            op.update_free(&mut fpcs.summary, false, rp);
        }
        // Statement post
        assert!(fpcs.repackings.is_empty());
        fpcs.apply_pre_effect = false;
        fpcs.visit_statement(stmt, loc);
        assert!(fpcs.repackings.is_empty());
        // Consistency
        fpcs.summary.consistency_check(rp);
        // Couplings bound unset
        fpcs.bound.borrow_mut().0 = None;

        // Only apply coupling ops after
        let cg_after = cg.next(loc);
        // Couplings
        for c in cg_after.couplings {
            c.update_free(self, false);
        }
        assert!(self.compare(&cg_after.state), "{loc:?}");
    }

    #[tracing::instrument(name = "CouplingState::compare", level = "trace")]
    fn compare(&self, other: &Graph) -> bool {
        // println!("Compare");
        for (sub, v) in self.blocks.iter_enumerated() {
            let blocks: FxHashSet<_> = other.nodes[sub].true_edges().into_iter().collect();
            // println!("Compare {sub:?} blocks: {v:?} == {blocks:?}");
            if v != &blocks {
                println!("{sub:?} blocks: {v:?} != {blocks:?}");
                return false;
            }
        }
        true
    }

    #[tracing::instrument(name = "mk_capability_upper_bound", level = "trace")]
    fn mk_capability_upper_bound(&self) -> impl Fn(Place<'tcx>) -> CapabilityKind + '_ {
        move |place| self.capability_upper_bound(place)
    }
    #[tracing::instrument(name = "capability_upper_bound", level = "debug")]
    fn capability_upper_bound(&self, place: Place<'tcx>) -> CapabilityKind {
        let mut upper_bound = CapabilityKind::Exclusive;
        for proj in place.projection_refs(self.cgx.rp) {
            match proj {
                None => upper_bound = CapabilityKind::Exclusive,
                Some((_, _, Mutability::Not)) => upper_bound = CapabilityKind::Read,
                Some((region, _, Mutability::Mut)) => {
                    let r = region.as_var(); // Could this not be a var?
                    if self.has_real_blockers(r) {
                        return CapabilityKind::None;
                    }
                }
            }
        }
        tracing::debug!("upper_bound: {:?}", upper_bound);
        for borrow in self.active_borrows() {
            assert!(self.has_real_blockers(borrow.region));
            // Places related?
            if let Some(bound) = upper_bound_borrow(place, borrow, self.cgx.rp) {
                upper_bound = upper_bound.minimum(bound).unwrap();
                // Early return
                if upper_bound.is_none() {
                    return upper_bound;
                }
            }
        }
        upper_bound
    }
    fn active_borrows(&self) -> impl Iterator<Item = &BorrowData<'tcx>> + '_ {
        self.blocked_by
            .iter_enumerated()
            .filter(|(region, blockers)| {
                !blockers.is_empty() && !self.waiting_to_activate.contains(region)
            })
            .flat_map(move |(region, _)| self.cgx.region_info.map.get(region).get_borrow())
    }
    fn has_real_blockers(&self, region: RegionVid) -> bool {
        let scc = self.calculate_scc(region);
        let fn_region = self.cgx.region_info.function_region;
        scc.iter().any(|r| {
            self.blocked_by[*r]
                .iter()
                .any(|blocker| !scc.contains(blocker) && *blocker != fn_region)
        })
        // self.blocked_by[region].iter().copied().any(|r| {
        //     let r = self.cgx.region_info.map.get(r);
        //     !r.universal() && !r.is_borrow()
        // })
    }
    fn calculate_scc(&self, region: RegionVid) -> FxHashSet<RegionVid> {
        let mut visited_out: FxHashSet<_> = [region, self.cgx.region_info.static_region]
            .into_iter()
            .collect();
        let mut stack = vec![region, self.cgx.region_info.static_region];
        while let Some(next) = stack.pop() {
            let blocks = self.blocks[next]
                .iter()
                .copied()
                .filter(|r| visited_out.insert(*r));
            stack.extend(blocks);
        }
        let mut visited_in: FxHashSet<_> = [region].into_iter().collect();
        let mut stack = vec![region];
        while let Some(next) = stack.pop() {
            let blocked_by = self.blocked_by[next]
                .iter()
                .copied()
                .filter(|r| visited_in.insert(*r));
            stack.extend(blocked_by);
        }
        visited_out.intersection(&visited_in).copied().collect()
    }
}

#[tracing::instrument(name = "upper_bound_borrow", level = "trace", skip(rp), ret)]
fn upper_bound_borrow<'tcx>(
    place: Place<'tcx>,
    borrow: &BorrowData<'tcx>,
    rp: PlaceRepacker<'_, 'tcx>,
) -> Option<CapabilityKind> {
    let borrowed = borrow.borrowed_place.into();
    place.partial_cmp(borrowed).map(|cmp| {
        let lower_bound = if cmp.is_prefix()
            && borrowed
                .projection_tys(rp)
                .skip(place.projection.len())
                .any(|(ty, _)| ty.ty.is_any_ptr())
        {
            CapabilityKind::Write
        } else {
            CapabilityKind::None
        };
        let kind = match borrow.kind {
            BorrowKind::Shared => CapabilityKind::Read,
            BorrowKind::Shallow if cmp.is_suffix() => CapabilityKind::Exclusive,
            BorrowKind::Shallow => CapabilityKind::Read,
            BorrowKind::Mut { .. } => CapabilityKind::None,
        };
        lower_bound.sum(kind).unwrap()
    })
}

impl CouplingOp {
    #[tracing::instrument(name = "CouplingOp::update_free", level = "trace")]
    fn update_free<'tcx>(&self, cg_state: &mut CouplingState, is_cleanup: bool) {
        match self {
            CouplingOp::Add(block) => block.update_free(cg_state, is_cleanup),
            CouplingOp::Remove(remove, new_blocks) => {
                Self::remove(cg_state, *remove);
                for block in new_blocks {
                    block.update_free(cg_state, is_cleanup);
                }
            }
            CouplingOp::Activate(region) => {
                let contained = cg_state.waiting_to_activate.remove(region);
                assert!(contained);
            }
        }
    }
    fn remove(cg_state: &mut CouplingState, remove: RegionVid) {
        let blocks = std::mem::replace(&mut cg_state.blocks[remove], FxHashSet::default());
        for block in blocks {
            cg_state.blocked_by[block].remove(&remove);
        }
        let blocked_by = std::mem::replace(&mut cg_state.blocked_by[remove], FxHashSet::default());
        for block_by in blocked_by {
            cg_state.blocks[block_by].remove(&remove);
        }
    }
}

impl Block {
    fn update_free<'tcx>(self, cg_state: &mut CouplingState, is_cleanup: bool) {
        let Block {
            sup,
            sub,
            waiting_to_activate,
        } = self;
        assert!(!cg_state.cgx.region_info.map.get(sub).is_borrow());
        if waiting_to_activate && cg_state.waiting_to_activate.insert(sup) {
            assert!(cg_state.blocked_by[sup].is_empty());
        }
        cg_state.blocks[sub].insert(sup);
        cg_state.blocked_by[sup].insert(sub);
    }
}
