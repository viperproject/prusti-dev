// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::data_structures::fx::FxHashMap;

use crate::{
    repack::triple::ModifiesFreeState, permission::FreeState, MicroBasicBlocks, permission::PermissionKind,
    permission::PermissionLocal, PlaceOrdering, RepackOp, Repacks, utils::PlaceRepacker,
};

pub(crate) fn check<'tcx>(bbs: &MicroBasicBlocks<'tcx>, rp: PlaceRepacker<'_, 'tcx>) {
    for bb in bbs.basic_blocks.iter() {
        let mut curr_state = bb.get_start_state().clone();
        // Consistency
        curr_state.consistency_check(rp);
        for stmt in bb.statements.iter() {
            // Pre-state
            let pcs = stmt.repack_operands.as_ref().unwrap();
            assert_eq!(pcs.state(), &curr_state);
            // Repacks
            pcs.repacks().update_free(&mut curr_state, false, rp);
            // Consistency
            curr_state.consistency_check(rp);
            // Statement
            stmt.get_update(curr_state.len())
                .update_free(&mut curr_state);
            // Consistency
            curr_state.consistency_check(rp);
        }
        // Pre-state
        let pcs = bb.terminator.repack_operands.as_ref().unwrap();
        assert_eq!(pcs.state(), &curr_state);
        // Repacks
        pcs.repacks().update_free(&mut curr_state, false, rp);
        // Consistency
        curr_state.consistency_check(rp);
        // Terminator
        bb.terminator
            .get_update(curr_state.len())
            .update_free(&mut curr_state);
        // Consistency
        curr_state.consistency_check(rp);
        // Join repacks
        let pcs = bb.terminator.repack_join.as_ref().unwrap();
        assert_eq!(pcs.state(), &curr_state);
        for succ in bb.terminator.original_kind.successors() {
            let mut curr_state = curr_state.clone();
            // No repack means that `succ` only has one predecessor
            if let Some(repack) = pcs.repacks().get(&succ) {
                repack.update_free(&mut curr_state, bbs.basic_blocks[succ].is_cleanup, rp);
                // Consistency
                curr_state.consistency_check(rp);
            }
            assert_eq!(
                bbs.basic_blocks[succ].get_start_state(),
                &curr_state,
                "{succ:?}"
            );
        }
    }
}

impl<'tcx> Repacks<'tcx> {
    #[tracing::instrument(level = "debug", skip(rp))]
    fn update_free(
        &self,
        state: &mut FreeState<'tcx>,
        can_dealloc: bool,
        rp: PlaceRepacker<'_, 'tcx>,
    ) {
        for rpck in &**self {
            match rpck {
                RepackOp::Weaken(place, from, to) => {
                    let curr_state = state[place.local].get_allocated_mut();
                    let old = curr_state.insert(*place, *to);
                    assert_eq!(old, Some(*from), "{rpck:?}, {curr_state:?}");
                }
                &RepackOp::DeallocForCleanup(local) => {
                    assert!(can_dealloc);
                    let curr_state = state[local].get_allocated_mut();
                    assert_eq!(curr_state.len(), 1);
                    assert_eq!(curr_state[&local.into()], PermissionKind::Uninit);
                    state[local] = PermissionLocal::Unallocated;
                }
                &RepackOp::DeallocUnknown(local) => {
                    assert!(!can_dealloc);
                    let curr_state = state[local].get_allocated_mut();
                    assert_eq!(curr_state.len(), 1);
                    assert_eq!(curr_state[&local.into()], PermissionKind::Uninit);
                    state[local] = PermissionLocal::Unallocated;
                }
                RepackOp::Pack(place, guide, kind) => {
                    assert_eq!(
                        place.partial_cmp(*guide),
                        Some(PlaceOrdering::Prefix),
                        "{rpck:?}"
                    );
                    let curr_state = state[place.local].get_allocated_mut();
                    let mut removed = curr_state
                        .drain_filter(|p, _| place.related_to(*p))
                        .collect::<FxHashMap<_, _>>();
                    let (p, others) = rp.expand_one_level(*place, *guide);
                    assert!(others
                        .into_iter()
                        .chain(std::iter::once(p))
                        .all(|p| removed.remove(&p).unwrap() == *kind));
                    assert!(removed.is_empty(), "{rpck:?}, {removed:?}");

                    let old = curr_state.insert(*place, *kind);
                    assert_eq!(old, None);
                }
                RepackOp::Unpack(place, guide, kind) => {
                    assert_eq!(
                        place.partial_cmp(*guide),
                        Some(PlaceOrdering::Prefix),
                        "{rpck:?}"
                    );
                    let curr_state = state[place.local].get_allocated_mut();
                    assert_eq!(
                        curr_state.remove(place),
                        Some(*kind),
                        "{rpck:?} ({:?})",
                        &**curr_state
                    );

                    let (p, others) = rp.expand_one_level(*place, *guide);
                    curr_state.insert(p, *kind);
                    curr_state.extend(others.into_iter().map(|p| (p, *kind)));
                }
            }
        }
    }
}
