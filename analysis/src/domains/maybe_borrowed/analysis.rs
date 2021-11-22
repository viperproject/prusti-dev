// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::AnalysisResult, domains::MaybeBorrowedState, AnalysisError,
    PointwiseState,
};
use log::{error, trace};
use rustc_borrowck::{consumers::RichLocation, BodyWithBorrowckFacts};
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir;

pub struct MaybeBorrowedAnalysis<'mir, 'tcx: 'mir> {
    body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'mir, 'tcx: 'mir> MaybeBorrowedAnalysis<'mir, 'tcx> {
    pub fn new(body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>) -> Self {
        MaybeBorrowedAnalysis { body_with_facts }
    }

    pub fn run_analysis(&self) -> AnalysisResult<PointwiseState<'mir, 'tcx, MaybeBorrowedState>> {
        let body = &self.body_with_facts.body;
        let location_table = &self.body_with_facts.location_table;
        let borrowck_in_facts = &self.body_with_facts.input_facts;
        let borrowck_out_facts = self.body_with_facts.output_facts.as_ref();
        let loan_issued_at = &borrowck_in_facts.loan_issued_at;
        let loan_live_at = &borrowck_out_facts.loan_live_at;
        let loan_issued_at_location: FxHashMap<_, mir::Location> = loan_issued_at
            .iter()
            .map(|&(_, loan, point_index)| {
                let rich_location = location_table.to_location(point_index);
                let location = match rich_location {
                    RichLocation::Start(loc) | RichLocation::Mid(loc) => loc,
                };
                (loan, location)
            })
            .collect();
        let mut analysis_state = PointwiseState::default(body);

        trace!("There are {} loan_live_at output facts", loan_live_at.len());
        for (&point_index, loans) in loan_live_at.iter() {
            let rich_location = location_table.to_location(point_index);
            if let RichLocation::Start(loan_live_at_location) = rich_location {
                trace!("  Location {:?}:", rich_location);
                let mut state = MaybeBorrowedState::default();
                for loan in loans {
                    let loan_location = loan_issued_at_location[loan];
                    let loan_stmt =
                        &body[loan_location.block].statements[loan_location.statement_index];
                    if let mir::StatementKind::Assign(box (_, rhs)) = &loan_stmt.kind {
                        if let mir::Rvalue::Ref(_region, borrow_kind, borrowed_place) = rhs {
                            trace!(
                                "    Loan {:?} is still borrowing {:?} as {:?}:",
                                loan,
                                borrowed_place,
                                borrow_kind,
                            );
                            let blocked_place = get_blocked_place(*borrowed_place);
                            trace!("      Blocked: {:?}", blocked_place);
                            match borrow_kind {
                                mir::BorrowKind::Shared => {
                                    state.maybe_shared_borrowed.insert(blocked_place);
                                }
                                mir::BorrowKind::Mut { .. } => {
                                    state.maybe_mut_borrowed.insert(blocked_place);
                                }
                                _ => {
                                    error!("Unexpected borrow kind: {:?}", borrow_kind);
                                    return Err(AnalysisError::UnsupportedStatement(loan_location));
                                }
                            }
                        } else {
                            error!("Unexpected RHS: {:?}", rhs);
                            return Err(AnalysisError::UnsupportedStatement(loan_location));
                        }
                    } else {
                        error!(
                            "Loan {:?} issued by an unexpected statement {:?} at {:?}",
                            loan, loan_stmt, loan_location,
                        );
                        return Err(AnalysisError::UnsupportedStatement(loan_location));
                    }
                }
                analysis_state.set_before(loan_live_at_location, state);
            }
        }

        // Set state_after_block
        for (block, block_data) in body.basic_blocks().iter_enumerated() {
            for &successor in block_data.terminator().successors() {
                let state = analysis_state
                    .lookup_before(mir::Location {
                        block: successor,
                        statement_index: 0,
                    })
                    .unwrap()
                    .to_owned();
                let state_after = analysis_state
                    .lookup_mut_after_block(block)
                    .get_mut(&successor)
                    .unwrap();
                debug_assert!(
                    (state_after.maybe_shared_borrowed.is_empty()
                        && state_after.maybe_mut_borrowed.is_empty())
                        || state_after == &state
                );
                *state_after = state;
            }
        }

        Ok(analysis_state)
    }
}

fn get_blocked_place(borrowed: mir::Place) -> mir::PlaceRef {
    for (place_ref, place_elem) in borrowed.iter_projections() {
        match place_elem {
            mir::ProjectionElem::Deref
            | mir::ProjectionElem::Index(..)
            | mir::ProjectionElem::ConstantIndex { .. }
            | mir::ProjectionElem::Subslice { .. } => {
                return place_ref;
            }
            mir::ProjectionElem::Field(..) | mir::ProjectionElem::Downcast(..) => {
                // Continue
            }
        }
    }
    borrowed.as_ref()
}
