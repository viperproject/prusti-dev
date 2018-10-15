// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::hir::def_id::DefId;
use rustc::hir;
use rustc::mir;
use rustc::ty;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use super::borrowck::{facts, regions};
use std::fs::File;
use polonius_engine::{Algorithm, Output, Atom};
use std::path::PathBuf;

#[derive(Clone, Debug)]
pub struct ExpiringBorrow<'tcx> {
    pub expiring: mir::Place<'tcx>,
    pub restored: mir::Rvalue<'tcx>,
    pub location: mir::Location,
}

pub struct PoloniusInfo<'a, 'tcx: 'a> {
    mir: &'a mir::Mir<'tcx>,
    borrowck_in_facts: facts::AllInputFacts,
    borrowck_out_facts: facts::AllOutputFacts,
    interner: facts::Interner,
    loan_position: HashMap<facts::Loan, mir::Location>,
    call_magic_wands: HashMap<facts::Loan, mir::Local>,
}

impl<'a, 'tcx: 'a> PoloniusInfo<'a, 'tcx> {
    pub fn new(tcx: ty::TyCtxt, def_id: DefId, mir: &'a mir::Mir<'tcx>) -> Self {
        // Read Polonius facts.
        let def_path = tcx.hir.def_path(def_id);
        let dir_path = PathBuf::from("nll-facts").join(def_path.to_filename_friendly_no_crate());
        debug!("Reading facts from: {:?}", dir_path);
        let mut facts_loader = facts::FactLoader::new();
        facts_loader.load_all_facts(&dir_path);

        // Read relations between region IDs and local variables.
        let renumber_path = PathBuf::from(format!(
            "log/mir/rustc.{}.-------.renumber.0.mir",
            def_path.to_filename_friendly_no_crate()));
        debug!("Renumber path: {:?}", renumber_path);
        let variable_regions = regions::load_variable_regions(&renumber_path).unwrap();

        //let mir = tcx.mir_validated(def_id).borrow();

        let mut call_magic_wands = HashMap::new();

        let mut all_facts = facts_loader.facts;
        {
            // TODO: Refactor.
            // The code that adds a creation of a new borrow for each
            // move of a borrow.

            // Find the last loan index.
            let mut last_loan_id = 0;
            for (_, loan, _) in all_facts.borrow_region.iter() {
                if loan.index() > last_loan_id {
                    last_loan_id = loan.index();
                }
            }
            last_loan_id += 1;

            // Create a map from points to (region1, region2) vectors.
            let universal_region = &all_facts.universal_region;
            let mut outlives_at_point = HashMap::new();
            for (region1, region2, point) in all_facts.outlives.iter() {
                if !universal_region.contains(region1) && !universal_region.contains(region2) {
                    let outlives = outlives_at_point.entry(point).or_insert(vec![]);
                    outlives.push((region1, region2));
                }
            }

            // Create new borrow_region facts for points where is only one outlives
            // fact and there is not a borrow_region fact already.
            let borrow_region = &mut all_facts.borrow_region;
            for (point, mut regions) in outlives_at_point {
                if borrow_region.iter().all(|(_, _, loan_point)| loan_point != point) {
                    if regions.len() > 1 {
                        let location = facts_loader.interner.get_point(*point).location.clone();
                        for &(region1, region2) in regions.iter() {
                            debug!("{:?} {:?} {:?}", location, region1, region2);
                        }
                        let call_destination = get_call_destination(&mir, location);
                        if let Some(place) = call_destination {
                            match place {
                                mir::Place::Local(local) => {
                                    let var_region = variable_regions.get(&local);
                                    debug!("var_region = {:?}", var_region);
                                    let loan = facts::Loan::from(last_loan_id);
                                    borrow_region.push(
                                        (*var_region.unwrap(),
                                         loan,
                                         *point));
                                    last_loan_id += 1;
                                    call_magic_wands.insert(loan, local);
                                }
                                x => unimplemented!("{:?}", x)
                            }
                        }
                    } else {
                        let (_region1, region2) = regions.pop().unwrap();
                        borrow_region.push((*region2, facts::Loan::from(last_loan_id), *point));
                        last_loan_id += 1;
                    }
                }
            }
        }

        let output = Output::compute(&all_facts, Algorithm::Naive, true);

        let interner = facts_loader.interner;
        let loan_position = all_facts.borrow_region
            .iter()
            .map(|&(_, loan, point_index)| {
                let point = interner.get_point(point_index);
                (loan, point.location)
            })
            .collect();

        PoloniusInfo {
            mir,
            borrowck_in_facts: all_facts,
            borrowck_out_facts: output,
            interner,
            loan_position,
            call_magic_wands
        }
    }

    fn get_point(&self, location: mir::Location, point_type: facts::PointType) -> facts::PointIndex {
        let point = facts::Point {
            location: location,
            typ: point_type,
        };
        self.interner.get_point_index(&point)
    }

    /// Get loans that dye at the given location.
    fn get_dying_loans(&self, location: mir::Location) -> Vec<facts::Loan> {
        let start_point = self.get_point(location, facts::PointType::Start);
        let mid_point = self.get_point(location, facts::PointType::Mid);

        if let Some(mid_loans) = self.borrowck_out_facts.borrow_live_at.get(&mid_point) {
            let mut mid_loans = mid_loans.clone();
            mid_loans.sort();
            let default_vec = vec![];
            let start_loans = self.borrowck_out_facts
                .borrow_live_at
                .get(&start_point)
                .unwrap_or(&default_vec);
            let mut start_loans = start_loans.clone();
            start_loans.sort();
            debug!("start_loans = {:?}", start_loans);
            debug!("mid_loans = {:?}", mid_loans);
            // Loans are created in mid point, so mid_point may contain more loans than the start
            // point.
            assert!(start_loans.iter().all(|loan| mid_loans.contains(loan)));

            let successors = self.get_successors(location);

            // Filter loans that are not missing in all successors.
            mid_loans
                .into_iter()
                .filter(|loan| {
                    !successors
                        .iter()
                        .any(|successor_location| {
                            let point = self.get_point(*successor_location, facts::PointType::Start);
                            self.borrowck_out_facts
                                .borrow_live_at
                                .get(&point)
                                .map_or(false, |successor_loans| {
                                    successor_loans.contains(loan)
                                })
                        })
                })
                .collect()
        } else {
            assert!(self.borrowck_out_facts.borrow_live_at.get(&start_point).is_none());
            vec![]
        }
    }

    pub fn get_expiring_borrows(&self, location: mir::Location) -> Vec<ExpiringBorrow<'tcx>> {
        let mut expiring_borrows = vec![];
        for loan in self.get_dying_loans(location).iter() {
            let loan_location = self.loan_position[loan];
            let mir_block = &self.mir[loan_location.block];
            debug_assert!(loan_location.statement_index < mir_block.statements.len());
            let mir_stmt = &mir_block.statements[loan_location.statement_index];
            match mir_stmt.kind {
                mir::StatementKind::Assign(ref lhs_place, ref rvalue) => {
                    expiring_borrows.push(
                        ExpiringBorrow {
                            expiring: lhs_place.clone(),
                            restored: rvalue.clone(),
                            location: loan_location
                        }
                    )
                }

                ref x => unreachable!("Borrow starts at statement {:?}", x),
            }
        }
        expiring_borrows
    }

    fn get_successors(&self, location: mir::Location) -> Vec<mir::Location> {
        let statements_len = self.mir[location.block].statements.len();
        if location.statement_index < statements_len {
            vec![mir::Location {
                statement_index: location.statement_index + 1,
                .. location
            }]
        } else {
            let mut successors = Vec::new();
            for successor in self.mir[location.block].terminator.as_ref().unwrap().successors() {
                successors.push(mir::Location {
                    block: *successor,
                    statement_index: 0,
                });
            }
            successors
        }
    }

    /*
    /// `package` – should it also try to compute the package statements?
    pub fn write_magic_wands(&mut self, package: bool,
                         location: mir::Location) -> Result<(), io::Error> {
        // TODO: Refactor out this code that computes magic wands.
        let blocker = mir::RETURN_PLACE;
        //TODO: Check if it really is always start and not the mid point.
        let start_point = self.get_point(location, facts::PointType::Start);

        if let Some(region) = self.variable_regions.get(&blocker) {
            write_graph!(self, "<tr>");
            write_graph!(self, "<td colspan=\"2\">Magic wand</td>");
            let subset_map = &self.borrowck_out_facts.subset;
            if let Some(ref subset) = subset_map.get(&start_point).as_ref() {
                let mut blocked_variables = Vec::new();
                if let Some(blocked_regions) = subset.get(&region) {
                    for blocked_region in blocked_regions.iter() {
                        if blocked_region == region {
                            continue;
                        }
                        if let Some(local) = self.find_variable(*blocked_region) {
                            blocked_variables.push(format!("{:?}:{:?}", local, blocked_region));
                        }
                    }
                    write_graph!(self, "<td colspan=\"7\">{:?}:{:?} --* {}</td>",
                                 blocker, region, to_sorted_string!(blocked_variables));
                } else {
                    write_graph!(self, "<td colspan=\"7\">BUG: no blocked region</td>");
                }
            } else {
                write_graph!(self, "<td colspan=\"7\">BUG: no subsets</td>");
            }
            write_graph!(self, "</tr>");
            if package {
                let restricts_map = &self.borrowck_out_facts.restricts;
                write_graph!(self, "<tr>");
                write_graph!(self, "<td colspan=\"2\">Package</td>");
                if let Some(ref restricts) = restricts_map.get(&start_point).as_ref() {
                    if let Some(loans) = restricts.get(&region) {
                        let loans: Vec<_> = loans.iter().cloned().collect();
                        write_graph!(self, "<td colspan=\"7\">{}", to_sorted_string!(loans));
                        self.write_reborrowing_trees(&loans)?;
                        write_graph!(self, "</td>");
                    } else {
                        write_graph!(self, "<td colspan=\"7\">BUG: no loans</td>");
                    }
                } else {
                    write_graph!(self, "<td colspan=\"7\">BUG: no restricts</td>");
                }
                write_graph!(self, "</tr>");
            }
        }
        Ok(())
    }

    fn write_reborrowing_trees(&self, loans: &[facts::Loan]) -> Result<(), io::Error> {
        // Find minimal elements that are the tree roots.
        let mut roots = Vec::new();
        for &loan in loans.iter() {
            let is_smallest = !loans
                .iter()
                .any(|&other_loan| {
                    self.additional_facts.reborrows.contains(&(other_loan, loan))
                });
            if is_smallest {
                roots.push(loan);
            }
        }
        // Reconstruct the tree from each root.
        for &root in roots.iter() {
            write_graph!(self, "<br />");
            self.write_reborrowing_tree(loans, root)?;
        }
        Ok(())
    }

    fn write_reborrowing_tree(&self, loans: &[facts::Loan],
                              node: facts::Loan) -> Result<(), io::Error> {
        if let Some(local) = self.call_magic_wands.get(&node) {
            let var_region = self.variable_regions[&local];
            write_graph!(self, "apply({:?}, {:?}:{:?})", node, local, var_region);
        } else {
            write_graph!(self, "{:?}", node);
        }
        let mut children = Vec::new();
        for &loan in loans.iter() {
            if self.additional_facts.reborrows_direct.contains(&(node, loan)) {
                children.push(loan);
            }
        }
        if children.len() == 1 {
            write_graph!(self, "{}", to_html_display!("->"));
            let child = children.pop().unwrap();
            self.write_reborrowing_tree(loans, child);
        } else if children.len() > 1 {
            write_graph!(self, "{}", to_html_display!("-> ("));
            for child in children {
                self.write_reborrowing_tree(loans, child);
                write_graph!(self, ",");
            }
            write_graph!(self, ")");
        }
        Ok(())
    }
    */
}

/// Extract the call terminator at the location. Otherwise return None.
fn get_call_destination<'tcx>(mir: &mir::Mir<'tcx>,
                        location: mir::Location) -> Option<mir::Place<'tcx>> {
    let mir::BasicBlockData { ref statements, ref terminator, .. } = mir[location.block];
    if statements.len() != location.statement_index {
        return None;
    }
    match terminator.as_ref().unwrap().kind {
        mir::TerminatorKind::Call { ref destination, .. } => {
            if let Some((ref place, _)) = destination {
                Some(place.clone())
            } else {
                None
            }
        }
        ref x => {
            panic!("Expected call, got {:?} at {:?}", x, location);
        }
    }
}