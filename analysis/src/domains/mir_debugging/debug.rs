// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// Tools for debugging the MIR and MicroMir

use crate::mir_utils::get_blocked_place;
use log::error;
use rustc_borrowck::{consumers::RichLocation, BodyWithBorrowckFacts};
use rustc_data_structures::stable_map::FxHashMap;
use rustc_middle::{mir, mir::Location, ty::TyCtxt};
use rustc_span::def_id::DefId;

pub fn pprint_loan_analysis<'mir, 'tcx: 'mir>(
    facts: &'mir BodyWithBorrowckFacts<'tcx>,
    tcx: TyCtxt<'tcx>,
    _def_id: DefId,
) {
    let body = &facts.body;
    let basic_blocks = &body.basic_blocks();
    let location_table = &facts.location_table;
    let borrowck_in_facts = &facts.input_facts;
    let borrowck_out_facts = &facts.output_facts.as_ref();
    let loan_issued_at = &borrowck_in_facts.loan_issued_at;
    let loan_live_at = &borrowck_out_facts.loan_live_at;
    let origin_live_on_entry = &borrowck_out_facts.origin_live_on_entry;
    let origin_contains_loan_at = &borrowck_out_facts.origin_contains_loan_at;
    let known_contains = &borrowck_out_facts.known_contains;
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
    // let mut analysis_state: PointwiseState<MaybeBorrowedState> = PointwiseState::default(body);

    println!("known contains ({}):", known_contains.len());
    for (o, loans) in known_contains.iter() {
        print!("\t{:#?}: ", o);
        for l in loans {
            print!("{:#?}, ", l);
        }
    }
    println!();
    println!();

    println!("loan_killed_at:",);
    for (loan, point) in &borrowck_in_facts.loan_killed_at {
        println!("\t\t\t{:#?}: {:#?} ", loan, point);
    }
    println!();
    println!();

    println!("loan_invalidated_at:",);
    for (loan, point) in &borrowck_in_facts.loan_invalidated_at {
        println!("\t\t\t{:#?}: {:#?} ", loan, point);
    }

    println!();
    println!();

    println!("loan_issued_at:",);
    for (origin, loan, point) in &borrowck_in_facts.loan_issued_at {
        println!("\t\t\t{:#?} ({:#?}): {:#?} ", loan, origin, point);
    }

    println!();
    println!();

    let mut loc: Location;
    for (bbno, bbdata) in (&basic_blocks).iter_enumerated() {
        println!("\n--------------- {:#?} ---------------", bbno);
        loc = Location {
            block: bbno,
            statement_index: 0,
        };

        /* Copied and modified from maybe_borrowed analysis */
        for stmt in bbdata.statements.iter() {
            println!("\t{:#?}", stmt);
            println!("\t\tLoc (start): {:#?}", &location_table.start_index(loc));
            println!("\t\tLoc (mid): {:#?}", &location_table.mid_index(loc));
            print!("\t\tOrigins live at (start) ");
            if let Some(origins) = origin_live_on_entry.get(&location_table.start_index(loc)) {
                for o in origins {
                    print!("{:#?}, ", o);
                }
                println!();
            } else {
                println!("\t\t\tNone");
            }

            println!("\t\tOrigin contains loan at (start): ");
            if let Some(ds) = borrowck_out_facts
                .origin_contains_loan_at
                .get(&location_table.start_index(loc))
            {
                for (d, dd) in ds {
                    print!("\t\t\t{:#?}: ", d);
                    for i in dd {
                        print!("{:#?}, ", i);
                    }
                    println!();
                }
                println!();
            } else {
                println!("\t\t\tNone");
            }

            println!("\t\tSubsets (start): ");
            if let Some(ds) = borrowck_out_facts
                .subset
                .get(&location_table.start_index(loc))
            {
                for (d, dd) in ds {
                    print!("\t\t\t{:#?}: ", d);
                    for i in dd {
                        print!("{:#?}, ", i);
                    }
                    println!();
                }
                println!();
            } else {
                println!("\t\t\tNone");
            }

            if let Some(loans) = loan_live_at.get(&location_table.start_index(loc)) {
                println!("\t\tlive loans (start):");
                for loan in loans {
                    let loan_location = loan_issued_at_location[loan];
                    let loan_stmt =
                        &body[loan_location.block].statements[loan_location.statement_index];
                    if let mir::StatementKind::Assign(box (lhs, rhs)) = &loan_stmt.kind {
                        if let mir::Rvalue::Ref(_region, borrow_kind, borrowed_place) = rhs {
                            println!(
                                "\t\t\tLoan {:?}: {:?} = & {:?} {:?}",
                                loan, lhs, borrow_kind, borrowed_place,
                            );
                            let blocked_place = get_blocked_place(tcx, (*borrowed_place).into());
                            println!("\t\t\t\tBlocking {:?}: {:?}", borrow_kind, blocked_place);
                        } else {
                            error!("Unexpected RHS: {:?}", rhs);
                        }
                    } else {
                        error!(
                            "Loan {:?} issued by an unexpected statement {:?} at {:?}",
                            loan, loan_stmt, loan_location,
                        );
                    }
                }
            }

            print!("\t\tlive origins (mid): ");
            if let Some(origins) = origin_live_on_entry.get(&location_table.mid_index(loc)) {
                for o in origins {
                    print!("{:#?}, ", o);
                }
                println!();
            } else {
                println!("\t\t\tNone");
            }

            println!("\t\torigin contains loan at (mid): ");
            if let Some(ds) = borrowck_out_facts
                .origin_contains_loan_at
                .get(&location_table.mid_index(loc))
            {
                for (d, dd) in ds {
                    print!("\t\t\t{:#?}: ", d);
                    for i in dd {
                        print!("{:#?}, ", i);
                    }
                    println!();
                }
                println!();
            } else {
                println!("\t\t\tNone");
            }

            println!("\t\tsubsets (mid): ");
            if let Some(ds) = borrowck_out_facts
                .subset
                .get(&location_table.mid_index(loc))
            {
                for (d, dd) in ds {
                    print!("\t\t\t{:#?}: ", d);
                    for i in dd {
                        print!("{:#?}, ", i);
                    }
                    println!();
                }
                println!();
            } else {
                println!("\t\t\tNone");
            }

            if let Some(loans) = loan_live_at.get(&location_table.mid_index(loc)) {
                println!("\t\tlive loans (mid): ");
                for loan in loans {
                    let loan_location = loan_issued_at_location[loan];
                    let loan_stmt =
                        &body[loan_location.block].statements[loan_location.statement_index];
                    if let mir::StatementKind::Assign(box (lhs, rhs)) = &loan_stmt.kind {
                        if let mir::Rvalue::Ref(_region, borrow_kind, borrowed_place) = rhs {
                            println!(
                                "\t\t\t\tLoan {:?}: {:?} = & {:?} {:?}",
                                loan, lhs, borrow_kind, borrowed_place,
                            );
                            let blocked_place = get_blocked_place(tcx, (*borrowed_place).into());
                            println!("\t\t\t\tBlocking {:?}: {:?}", borrow_kind, blocked_place);
                        } else {
                            error!("Unexpected RHS: {:?}", rhs);
                        }
                    } else {
                        error!(
                            "Loan {:?} issued by an unexpected statement {:?} at {:?}",
                            loan, loan_stmt, loan_location,
                        );
                    }
                }
            }
            loc.statement_index += 1;
        }

        println!("TERMINATOR: {:#?}", bbdata.terminator().kind);
    }
}
