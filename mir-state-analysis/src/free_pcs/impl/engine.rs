// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    dataflow::{Analysis, AnalysisDomain, CallReturnPlaces},
    index::vec::Idx,
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, Local, Location, Statement, Terminator, RETURN_PLACE,
        },
        ty::TyCtxt,
    },
};

use crate::{utils::PlaceRepacker, CapabilityKind, CapabilityLocal, Fpcs};

pub(crate) struct FreePlaceCapabilitySummary<'a, 'tcx>(pub(crate) PlaceRepacker<'a, 'tcx>);
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
        let always_live = self.0.always_live_locals();
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(body.arg_count);
        for (local, cap) in state.summary.iter_enumerated_mut() {
            if local == return_local {
                let old = cap
                    .get_allocated_mut()
                    .insert(local.into(), CapabilityKind::Write);
                assert!(old.is_some());
            } else if local <= last_arg {
                let old = cap
                    .get_allocated_mut()
                    .insert(local.into(), CapabilityKind::Exclusive);
                assert!(old.is_some());
            } else if always_live.contains(local) {
                // TODO: figure out if `always_live` should start as `Uninit` or `Exclusive`
                let al_cap = if true {
                    CapabilityKind::Write
                } else {
                    CapabilityKind::Exclusive
                };
                let old = cap.get_allocated_mut().insert(local.into(), al_cap);
                assert!(old.is_some());
            } else {
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
        state.repackings.clear();
        state.visit_statement(statement, location);
    }

    fn apply_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        state.repackings.clear();
        state.visit_terminator(terminator, location);
    }

    fn apply_call_return_effect(
        &self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}
