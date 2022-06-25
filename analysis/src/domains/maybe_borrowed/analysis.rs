// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::AnalysisResult, domains::MaybeBorrowedState,
    mir_utils::get_blocked_place, AnalysisError, PointwiseState,
};
use log::{error, trace};
use prusti_rustc_interface::{
    borrowck::{consumers::RichLocation, BodyWithBorrowckFacts},
    data_structures::fx::FxHashMap,
    middle::{mir, ty::TyCtxt},
};

pub struct MaybeBorrowedAnalysis<'mir, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'mir, 'tcx: 'mir> MaybeBorrowedAnalysis<'mir, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>) -> Self {
        MaybeBorrowedAnalysis {
            tcx,
            body_with_facts,
        }
    }

    pub fn run_analysis(
        &self,
    ) -> AnalysisResult<PointwiseState<'mir, 'tcx, MaybeBorrowedState<'tcx>>> {
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
        let mut analysis_state: PointwiseState<MaybeBorrowedState> = PointwiseState::default(body);

        trace!("There are {} loan_live_at output facts", loan_live_at.len());
        for (&point_index, loans) in loan_live_at.iter() {
            let rich_location = location_table.to_location(point_index);
            if let RichLocation::Start(location) = rich_location {
                trace!("  Location {:?}:", rich_location);
                let state = analysis_state.lookup_mut_before(location).unwrap();
                for loan in loans {
                    let loan_location = loan_issued_at_location[loan];
                    let loan_stmt =
                        &body[loan_location.block].statements[loan_location.statement_index];
                    if let mir::StatementKind::Assign(box (lhs, rhs)) = &loan_stmt.kind {
                        if let mir::Rvalue::Ref(_region, borrow_kind, borrowed_place) = rhs {
                            trace!(
                                "    Loan {:?}: {:?} = & {:?} {:?}",
                                loan,
                                lhs,
                                borrow_kind,
                                borrowed_place,
                            );
                            let blocked_place =
                                get_blocked_place(self.tcx, (*borrowed_place).into());
                            trace!("      Blocking {:?}: {:?}", borrow_kind, blocked_place);
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
            }
        }

        // Set state_after_block
        for (block, block_data) in body.basic_blocks().iter_enumerated() {
            for successor in block_data.terminator().successors() {
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
