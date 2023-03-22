// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    data_structures::{fx::FxHashSet, graph::WithStartNode},
    dataflow::{storage, Analysis, ResultsCursor, AnalysisDomain, JoinSemiLattice, CallReturnPlaces,
        impls::{MaybeStorageLive, MaybeBorrowedLocals, MaybeRequiresStorage, MaybeLiveLocals}},
    index::vec::{Idx, IndexVec},
    middle::{
        mir::{visit::Visitor, Statement, Location, Terminator, Body, BasicBlock, HasLocalDecls, Local, RETURN_PLACE},
        ty::TyCtxt,
    },
};

use crate::{
    CapabilityKind, CapabilityLocal, utils::PlaceRepacker, RepackOp, CapabilityProjections, Fpcs, CapabilitySummary, PlaceOrdering
};

// pub fn test<'tcx>(body_ref: &Body<'tcx>, tcx: TyCtxt<'tcx>) {
//     let always_live_locals = storage::always_storage_live_locals(body_ref);

//     // Calculate when MIR locals have live storage. This gives us an upper bound of their
//     // lifetimes.
//     let mut storage_live = MaybeStorageLive::new(std::borrow::Cow::Borrowed(&always_live_locals))
//         .into_engine(tcx, body_ref)
//         .iterate_to_fixpoint()
//         .into_results_cursor(body_ref);

//     // Calculate the MIR locals which have been previously
//     // borrowed (even if they are still active).
//     let borrowed_locals_results =
//         MaybeBorrowedLocals.into_engine(tcx, body_ref).pass_name("generator").iterate_to_fixpoint();

//     let mut borrowed_locals_cursor =
//         ResultsCursor::new(body_ref, &borrowed_locals_results);

//     // Calculate the MIR locals that we actually need to keep storage around
//     // for.
//     let requires_storage_results = MaybeRequiresStorage::new(body_ref, &borrowed_locals_results)
//         .into_engine(tcx, body_ref)
//         .iterate_to_fixpoint();
//     let mut requires_storage_cursor =
//         ResultsCursor::new(body_ref, &requires_storage_results);

//     // Calculate the liveness of MIR locals ignoring borrows.
//     let mut liveness = MaybeLiveLocals
//         .into_engine(tcx, body_ref)
//         .pass_name("generator")
//         .iterate_to_fixpoint()
//         .into_results_cursor(body_ref);

//     println!("Done");
// }

pub(crate) struct FreePlaceCapabilitySummary<'a, 'tcx>(PlaceRepacker<'a, 'tcx>);
impl<'a, 'tcx> FreePlaceCapabilitySummary<'a, 'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>) -> Self {
        let repacker = PlaceRepacker::new(body, tcx);
        FreePlaceCapabilitySummary(repacker)
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for FreePlaceCapabilitySummary<'a, 'tcx> {
    type Domain = Fpcs<'a, 'tcx>;
    const NAME: &'static str = "free_pcs";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        Fpcs::new(self.0)
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        let always_live = storage::always_storage_live_locals(body);
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(body.arg_count);
        for (local, cap) in state.summary.iter_enumerated_mut() {
            if local == return_local {
                let old = cap.get_allocated_mut().insert(local.into(), CapabilityKind::Write);
                assert!(old.is_some());
            } else if local <= last_arg {
                let old = cap.get_allocated_mut().insert(local.into(), CapabilityKind::Exclusive(None));
                assert!(old.is_some());
            } else if always_live.contains(local) {
                // TODO: figure out if `always_live` should start as `Uninit` or `Exclusive`
                let al_cap = if true {
                    CapabilityKind::Write
                } else {
                    CapabilityKind::Exclusive(None)
                };
                let old = cap.get_allocated_mut().insert(local.into(), al_cap);
                assert!(old.is_some());
            }else {
                *cap = CapabilityLocal::Unallocated;
            }
        }
    }
}

impl<'a, 'tcx> Analysis<'tcx> for FreePlaceCapabilitySummary<'a, 'tcx> {
    fn apply_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        state.visit_statement(statement, location);
    }

    fn apply_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        state.visit_terminator(terminator, location);
    }

    fn apply_call_return_effect(
        &self,
        state: &mut Self::Domain,
        block: BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // todo!()
    }
}
