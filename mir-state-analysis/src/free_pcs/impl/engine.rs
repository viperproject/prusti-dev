// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    dataflow::{Analysis, AnalysisDomain},
    index::Idx,
    middle::{
        mir::{
            visit::Visitor, BasicBlock, Body, CallReturnPlaces, Local, Location, Statement,
            Terminator, TerminatorEdges, RETURN_PLACE,
        },
        ty::TyCtxt,
    },
};

use crate::{
    free_pcs::{CapabilityKind, CapabilityLocal, Fpcs},
    utils::PlaceRepacker,
};

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
        state.bottom = false;
        let always_live = self.0.always_live_locals();
        let return_local = RETURN_PLACE;
        let last_arg = Local::new(body.arg_count);
        for (local, cap) in state.summary.iter_enumerated_mut() {
            assert!(cap.is_unallocated());
            let new_cap = if local == return_local {
                CapabilityLocal::new(local, CapabilityKind::Write)
            } else if local <= last_arg {
                CapabilityLocal::new(local, CapabilityKind::Exclusive)
            } else if always_live.contains(local) {
                // TODO: figure out if `always_live` should start as `Uninit` or `Exclusive`
                let al_cap = if true {
                    CapabilityKind::Write
                } else {
                    CapabilityKind::Exclusive
                };
                CapabilityLocal::new(local, al_cap)
            } else {
                CapabilityLocal::Unallocated
            };
            *cap = new_cap;
        }
    }
}

impl<'a, 'tcx> Analysis<'tcx> for FreePlaceCapabilitySummary<'a, 'tcx> {
    #[tracing::instrument(
        name = "FreePlaceCapabilitySummary::apply_before_statement_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_before_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        state.repackings.clear();
        state.apply_pre_effect = true;
        state.visit_statement(statement, location);
    }
    #[tracing::instrument(
        name = "FreePlaceCapabilitySummary::apply_statement_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        state.repackings.clear();
        state.apply_pre_effect = false;
        state.visit_statement(statement, location);
    }

    #[tracing::instrument(
        name = "FreePlaceCapabilitySummary::apply_before_terminator_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_before_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        state.repackings.clear();
        state.apply_pre_effect = true;
        state.visit_terminator(terminator, location);
    }
    #[tracing::instrument(
        name = "FreePlaceCapabilitySummary::apply_terminator_effect",
        level = "debug",
        skip(self)
    )]
    fn apply_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        state.repackings.clear();
        state.apply_pre_effect = false;
        state.visit_terminator(terminator, location);
        terminator.edges()
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing to do here
    }
}
