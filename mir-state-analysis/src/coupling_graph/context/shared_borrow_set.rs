// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    index::bit_set::BitSet,
    dataflow::fmt::DebugWithContext, index::IndexVec, middle::mir::Local,
    borrowck::{borrow_set::{BorrowData, BorrowSet, TwoPhaseActivation, LocalsStateAtExit}, consumers::{BorrowIndex, PlaceExt}},
    middle::{mir::{ConstraintCategory, RETURN_PLACE, Location, Place, Rvalue, Body, traversal, visit::Visitor}, ty::{TyCtxt}},
};

// Identical to `rustc_borrowck/src/borrow_set.rs` but for shared borrows
#[derive(Debug, Clone)]
pub struct SharedBorrowSet<'tcx> {
    pub location_map: FxIndexMap<Location, BorrowData<'tcx>>,
    pub local_map: FxIndexMap<Local, FxIndexSet<BorrowIndex>>,
}

impl<'tcx> SharedBorrowSet<'tcx> {
    pub(crate) fn build(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        borrows: &BorrowSet<'tcx>,
    ) -> Self {
        let mut visitor = GatherBorrows {
            tcx,
            body: &body,
            location_map: Default::default(),
            local_map: Default::default(),
            locals_state_at_exit: &borrows.locals_state_at_exit,
        };

        for (block, block_data) in traversal::preorder(&body) {
            visitor.visit_basic_block_data(block, block_data);
        }

        Self {
            location_map: visitor.location_map,
            local_map: visitor.local_map,
        }
    }
}

struct GatherBorrows<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    location_map: FxIndexMap<Location, BorrowData<'tcx>>,
    local_map: FxIndexMap<Local, FxIndexSet<BorrowIndex>>,
    locals_state_at_exit: &'a LocalsStateAtExit,
}

impl<'a, 'tcx> Visitor<'tcx> for GatherBorrows<'a, 'tcx> {
    fn visit_assign(
        &mut self,
        assigned_place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) {
        if let &Rvalue::Ref(region, kind, borrowed_place) = rvalue {
            // Gather all borrows that the normal borrow-checker misses
            if !borrowed_place.ignore_borrow(self.tcx, self.body, self.locals_state_at_exit) {
                return;
            }

            let region = region.as_var();

            let borrow = BorrowData {
                kind,
                region,
                reserve_location: location,
                activation_location: TwoPhaseActivation::NotTwoPhase,
                borrowed_place,
                assigned_place: *assigned_place,
            };
            let (idx, _) = self.location_map.insert_full(location, borrow);
            let idx = BorrowIndex::from(idx);

            self.local_map.entry(borrowed_place.local).or_default().insert(idx);
        }

        self.super_assign(assigned_place, rvalue, location)
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let &Rvalue::Ref(region, kind, place) = rvalue {
            // double-check that we already registered a BorrowData for this

            let borrow_data = &self.location_map[&location];
            assert_eq!(borrow_data.reserve_location, location);
            assert_eq!(borrow_data.kind, kind);
            assert_eq!(borrow_data.region, region.as_var());
            assert_eq!(borrow_data.borrowed_place, place);
        }

        self.super_rvalue(rvalue, location)
    }
}
