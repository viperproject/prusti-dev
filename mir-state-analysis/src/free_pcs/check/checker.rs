// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
    middle::mir::{visit::Visitor, Location},
};

use crate::{
    utils::PlaceRepacker, CapabilityKind, CapabilityLocal, CapabilitySummary, Fpcs,
    FreePcsAnalysis, PlaceOrdering, RepackOp,
};

use super::consistency::CapabilityConistency;

pub(crate) fn check(mut results: FreePcsAnalysis<'_, '_>) {
    let rp = results.repacker();
    let body = rp.body();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let mut cursor = results.analysis_for_bb(block);
        let mut fpcs = Fpcs {
            summary: cursor.initial_state().clone(),
            repackings: Vec::new(),
            repacker: rp,
        };
        // Consistency
        fpcs.summary.consistency_check(rp);
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            let loc = Location {
                block,
                statement_index,
            };
            let fpcs_after = cursor.next().unwrap();
            assert_eq!(fpcs_after.location, loc);
            // Repacks
            for op in fpcs_after.repacks {
                op.update_free(&mut fpcs.summary, false, rp);
            }
            // Consistency
            fpcs.summary.consistency_check(rp);
            // Statement
            assert!(fpcs.repackings.is_empty());
            fpcs.visit_statement(stmt, loc);
            assert!(fpcs.repackings.is_empty());
            // Consistency
            fpcs.summary.consistency_check(rp);
        }
        let loc = Location {
            block,
            statement_index: data.statements.len(),
        };
        let fpcs_after = cursor.next().unwrap();
        assert_eq!(fpcs_after.location, loc);
        // Repacks
        for op in fpcs_after.repacks {
            op.update_free(&mut fpcs.summary, false, rp);
        }
        // Consistency
        fpcs.summary.consistency_check(rp);
        // Statement
        assert!(fpcs.repackings.is_empty());
        fpcs.visit_terminator(data.terminator(), loc);
        assert!(fpcs.repackings.is_empty());
        // Consistency
        fpcs.summary.consistency_check(rp);
        assert_eq!(&fpcs.summary, fpcs_after.state);

        let Err(fpcs_end) = cursor.next() else {
            panic!("Expected error at the end of the block");
        };

        for succ in fpcs_end.succs {
            // Repacks
            let mut from = fpcs.clone();
            for op in succ.repacks {
                op.update_free(
                    &mut from.summary,
                    body.basic_blocks[succ.location.block].is_cleanup,
                    rp,
                );
            }
            assert_eq!(&from.summary, succ.state);
        }
    }
}

impl<'tcx> RepackOp<'tcx> {
    #[tracing::instrument(level = "debug", skip(rp))]
    fn update_free(
        &self,
        state: &mut CapabilitySummary<'tcx>,
        can_dealloc: bool,
        rp: PlaceRepacker<'_, 'tcx>,
    ) {
        match self {
            RepackOp::Weaken(place, from, to) => {
                assert!(from >= to, "{self:?}");
                let curr_state = state[place.local].get_allocated_mut();
                let old = curr_state.insert(*place, *to);
                assert_eq!(old, Some(*from), "{self:?}, {curr_state:?}");
            }
            &RepackOp::DeallocForCleanup(local) => {
                assert!(can_dealloc);
                let curr_state = state[local].get_allocated_mut();
                assert_eq!(curr_state.len(), 1);
                assert!(
                    curr_state.contains_key(&local.into()),
                    "{self:?}, {curr_state:?}"
                );
                assert_eq!(curr_state[&local.into()], CapabilityKind::Write);
                state[local] = CapabilityLocal::Unallocated;
            }
            // &RepackOp::DeallocUnknown(local) => {
            //     assert!(!can_dealloc);
            //     let curr_state = state[local].get_allocated_mut();
            //     assert_eq!(curr_state.len(), 1);
            //     assert_eq!(curr_state[&local.into()], CapabilityKind::Write);
            //     state[local] = CapabilityLocal::Unallocated;
            // }
            RepackOp::Pack(place, guide, kind) => {
                assert_eq!(
                    place.partial_cmp(*guide),
                    Some(PlaceOrdering::Prefix),
                    "{self:?}"
                );
                let curr_state = state[place.local].get_allocated_mut();
                let mut removed = curr_state
                    .drain()
                    .filter(|(p, _)| place.related_to(*p))
                    .collect::<FxHashMap<_, _>>();
                let (p, others) = place.expand_one_level(*guide, rp);
                assert!(others
                    .into_iter()
                    .chain(std::iter::once(p))
                    .all(|p| removed.remove(&p).unwrap() == *kind));
                assert!(removed.is_empty(), "{self:?}, {removed:?}");

                let old = curr_state.insert(*place, *kind);
                assert_eq!(old, None);
            }
            RepackOp::Unpack(place, guide, kind) => {
                assert_eq!(
                    place.partial_cmp(*guide),
                    Some(PlaceOrdering::Prefix),
                    "{self:?}"
                );
                let curr_state = state[place.local].get_allocated_mut();
                assert_eq!(
                    curr_state.remove(place),
                    Some(*kind),
                    "{self:?} ({:?})",
                    &**curr_state
                );

                let (p, others) = place.expand_one_level(*guide, rp);
                curr_state.insert(p, *kind);
                curr_state.extend(others.into_iter().map(|p| (p, *kind)));
            }
        }
    }
}
