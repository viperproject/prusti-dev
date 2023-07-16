// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    data_structures::fx::FxHashMap,
    middle::mir::{visit::Visitor, Location, ProjectionElem},
};

use crate::{
    free_pcs::{
        CapabilityKind, CapabilityLocal, CapabilitySummary, Fpcs, FreePcsAnalysis, RepackOp,
    },
    utils::PlaceRepacker,
};

use super::consistency::CapabilityConistency;

pub(crate) fn check(mut results: FreePcsAnalysis<'_, '_>) {
    let rp = results.repacker();
    let body = rp.body();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let mut cursor = results.analysis_for_bb(block);
        let mut fpcs = Fpcs {
            summary: cursor.initial_state().clone(),
            bottom: false,
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
        self,
        state: &mut CapabilitySummary<'tcx>,
        is_cleanup: bool,
        rp: PlaceRepacker<'_, 'tcx>,
    ) {
        match self {
            RepackOp::StorageDead(local) => {
                let curr_state = state[local].get_allocated_mut();
                assert_eq!(curr_state.len(), 1);
                assert!(
                    curr_state.contains_key(&local.into()),
                    "{self:?}, {curr_state:?}"
                );
                assert_eq!(curr_state[&local.into()], CapabilityKind::Write);
                state[local] = CapabilityLocal::Unallocated;
            }
            RepackOp::IgnoreStorageDead(local) => {
                assert_eq!(state[local], CapabilityLocal::Unallocated);
                // Add write permission so that the `mir::StatementKind::StorageDead` can
                // deallocate without producing any repacks, which would cause the
                // `assert!(fpcs.repackings.is_empty());` above to fail.
                state[local] = CapabilityLocal::new(local, CapabilityKind::Write);
            }
            RepackOp::Weaken(place, from, to) => {
                assert!(from >= to, "{self:?}");
                let curr_state = state[place.local].get_allocated_mut();
                let old = curr_state.insert(place, to);
                assert_eq!(old, Some(from), "{self:?}, {curr_state:?}");
            }
            RepackOp::Expand(place, guide, kind) => {
                assert!(place.is_prefix_exact(guide), "{self:?}");
                assert_ne!(*guide.projection.last().unwrap(), ProjectionElem::Deref);
                let curr_state = state[place.local].get_allocated_mut();
                assert_eq!(
                    curr_state.remove(&place),
                    Some(kind),
                    "{self:?} ({curr_state:?})"
                );

                let (p, others, pkind) = place.expand_one_level(guide, rp);
                assert!(!pkind.is_deref());
                curr_state.insert(p, kind);
                curr_state.extend(others.into_iter().map(|p| (p, kind)));
            }
            RepackOp::Collapse(place, guide, kind) => {
                assert!(place.is_prefix_exact(guide), "{self:?}");
                assert_ne!(*guide.projection.last().unwrap(), ProjectionElem::Deref);
                let curr_state = state[place.local].get_allocated_mut();
                let mut removed = curr_state
                    .extract_if(|p, _| place.related_to(*p))
                    .collect::<FxHashMap<_, _>>();

                let (p, mut others, pkind) = place.expand_one_level(guide, rp);
                assert!(!pkind.is_deref());
                others.push(p);
                for other in others {
                    assert_eq!(removed.remove(&other), Some(kind), "{self:?}");
                }
                assert!(removed.is_empty(), "{self:?}, {removed:?}");
                let old = curr_state.insert(place, kind);
                assert_eq!(old, None);
            }
            RepackOp::Deref(place, kind, guide, to_kind) => {
                assert!(place.is_prefix_exact(guide), "{self:?}");
                assert_eq!(*guide.projection.last().unwrap(), ProjectionElem::Deref);
                let curr_state = state[place.local].get_allocated_mut();
                assert_eq!(
                    curr_state.remove(&place),
                    Some(kind),
                    "{self:?} ({curr_state:?})"
                );

                let (p, others, pkind) = place.expand_one_level(guide, rp);
                assert!(pkind.is_deref());
                if pkind.is_box() && kind.is_shallow_exclusive() {
                    assert_eq!(to_kind, CapabilityKind::Write);
                } else {
                    assert_eq!(to_kind, kind);
                }

                curr_state.insert(p, to_kind);
                assert!(others.is_empty());
            }
            RepackOp::Upref(place, to_kind, guide, kind) => {
                assert!(place.is_prefix_exact(guide), "{self:?}");
                assert_eq!(*guide.projection.last().unwrap(), ProjectionElem::Deref);
                let curr_state = state[place.local].get_allocated_mut();
                let mut removed = curr_state
                    .extract_if(|p, _| place.related_to(*p))
                    .collect::<FxHashMap<_, _>>();

                let (p, mut others, pkind) = place.expand_one_level(guide, rp);
                assert!(pkind.is_deref());
                others.push(p);
                for other in others {
                    assert_eq!(removed.remove(&other), Some(kind));
                }
                assert!(removed.is_empty(), "{self:?}, {removed:?}");

                if pkind.is_shared_ref() && !place.projects_shared_ref(rp) {
                    assert_eq!(kind, CapabilityKind::Read);
                    assert_eq!(to_kind, CapabilityKind::Exclusive);
                } else {
                    assert_eq!(to_kind, kind);
                }
                let old = curr_state.insert(place, to_kind);
                assert_eq!(old, None);
            }
        }
    }
}
