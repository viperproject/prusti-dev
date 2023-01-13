// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use itertools::Itertools;

use std::collections::{BTreeMap, BTreeSet};

use super::state::{Loan, Path, PointIndex, Region, Variable};
use crate::{
    abstract_interpretation::{AnalysisResult, FixpointEngine},
    domains::CouplingState,
    AnalysisError, PointwiseState,
};
use prusti_rustc_interface::{
    borrowck::{consumers::RichLocation, BodyWithBorrowckFacts},
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{BorrowKind, Location, Rvalue, StatementKind, TerminatorKind},
        ty::TyCtxt,
    },
    span::def_id::DefId,
};

pub struct CouplingAnalysis<'facts, 'mir: 'facts, 'tcx: 'mir> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    fact_table: &'facts FactTable<'tcx>,
    body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> CouplingAnalysis<'facts, 'mir, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        fact_table: &'facts FactTable<'tcx>,
        body_with_facts: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> Self {
        CouplingAnalysis {
            tcx,
            def_id,
            fact_table,
            body_with_facts,
        }
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> FixpointEngine<'mir, 'tcx>
    for CouplingAnalysis<'facts, 'mir, 'tcx>
{
    type State = CouplingState<'facts, 'mir, 'tcx>;

    fn def_id(&self) -> DefId {
        self.def_id
    }

    fn body(&self) -> &'mir mir::Body<'tcx> {
        &self.body_with_facts.body
    }

    fn new_bottom(&self) -> Self::State {
        // todo: remove stub
        Self::State::new_empty(self.body_with_facts, self.fact_table)
    }

    fn new_initial(&self) -> Self::State {
        // todo: remove stub
        Self::State::new_empty(self.body_with_facts, self.fact_table)
    }

    fn need_to_widen(counter: u32) -> bool {
        assert!(counter <= 2);
        false
    }

    fn apply_statement_effect(
        &self,
        state: &mut Self::State,
        location: mir::Location,
    ) -> AnalysisResult<()> {
        // todo: remove stub
        state.apply_statement_effect(location)
    }

    fn apply_terminator_effect(
        &self,
        state: &Self::State,
        location: mir::Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self::State)>> {
        state.apply_terminator_effect(location)
    }
}

// todo: Put
impl<'facts, 'mir: 'facts, 'tcx: 'mir>
    PointwiseState<'mir, 'tcx, CouplingState<'facts, 'mir, 'tcx>>
{
}

/// Struct containing lookups for all the Polonius facts
#[derive(Debug, Default)]
pub struct FactTable<'tcx> {
    /// Issue of a loan, into it's issuing origin, and a loan of a place
    loan_issues: LoanIssues<'tcx>,

    // Interpretation of regions in terms of places and temporaries
    origins: OriginPlaces<'tcx>,

    // Some points requre the LHS of an origin to be repacked to include a specific place
    origin_packing_at: OriginPacking<'tcx>,

    // Extra structural edges
    structural_edge: StructuralEdge<'tcx>,
}

/// Issue of a new loan. The assocciated region should represent a borrow temporary.
type LoanIssues<'tcx> = FxHashMap<PointIndex, Region>;
type OriginPacking<'tcx> = FxHashMap<PointIndex, Vec<(Region, OriginLHS<'tcx>)>>;
type StructuralEdge<'tcx> = FxHashMap<PointIndex, Vec<(SubsetBaseKind, Region, Region)>>;

/// Assignment between Origins and places
/// Precise relationship between these two are yet unconfirmed by the Polonius team
/// NOTE: The LHS of a origin is no necessarily this place, as it may be further unpacked.
/// NOTE: We don't know if this is a bijection yet, nor the full scope of Temporaries Polonius
/// uses (see: OriginLHS struct for the current characterization)
#[derive(Debug, Default)]
struct OriginPlaces<'tcx>(FxHashMap<Region, OriginLHS<'tcx>>);

impl<'tcx> OriginPlaces<'tcx> {
    // Attempt to add a new constraint to the origin mapping
    pub fn new_constraint(&mut self, r: Region, c: OriginLHS<'tcx>) {
        let normalized_c = self.normalize_origin_lhs(c);
        if let Some(old_lhs) = self.0.insert(r, normalized_c.clone()) {
            assert!(old_lhs == normalized_c);
        }
    }

    /// Rewrite c into a cannonical form for key equality
    /// eg. normalize_origin_lhs(*x) == normalize_origin_lhs(x)
    fn normalize_origin_lhs(&self, c: OriginLHS<'tcx>) -> OriginLHS<'tcx> {
        // fixme: Need to check that p is maximally packed if it is a place
        return c;
    }

    fn get_origin(&self, c: OriginLHS<'tcx>) -> Option<Region> {
        let normalized_c = self.normalize_origin_lhs(c);
        self.0
            .iter()
            .find(|(_, v)| **v == normalized_c)
            .map(|(k, v)| *k)
    }
}

#[derive(PartialEq, Eq, Clone)]
pub enum OriginLHS<'tcx> {
    Place(mir::Place<'tcx>),
    Loan(Loan),
}

impl<'tcx> std::fmt::Debug for OriginLHS<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Place(p) => f.write_fmt(format_args!("Place({:?})", p)),
            Self::Loan(l) => f.write_fmt(format_args!("Loan({:?})", l)),
        }
    }
}

/// Assignment and the associated subset_base fact
type Assignments<'tcx> = FxHashMap<PointIndex, (mir::Place<'tcx>, Region)>;

enum StatementKinds<'mir, 'tcx: 'mir> {
    Stmt(&'mir StatementKind<'tcx>),
    Term(&'mir TerminatorKind<'tcx>),
}

impl<'tcx> FactTable<'tcx> {
    // FIXME: Use a several-pass pattern to compute this (eg. arguments of kind &mut Self)
    pub fn new(mir: &BodyWithBorrowckFacts<'tcx>) -> AnalysisResult<Self> {
        let mut working_table = Self::default();
        Self::collect_subset_base_at(mir, &mut working_table)?;
        Self::compute_loan_issues(mir, &mut working_table)?;
        Self::characterize_subset_base(&mut working_table, mir)?;
        Self::compute_loan_assigned_at(mir, &mut working_table)?;
        Self::collect_loan_killed_at(mir, &mut working_table)?;
        Self::collect_origin_contains_loan_at(mir, &mut working_table)?;
        println!("[fact table]  {:#?}", working_table);
        return Ok(working_table);
    }

    fn collect_origin_contains_loan_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) -> AnalysisResult<()> {
        // fixme: todo
        Ok(())
    }

    fn collect_subset_base_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) -> AnalysisResult<()> {
        // fixme: todo
        Ok(())
    }

    fn collect_loan_killed_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) -> AnalysisResult<()> {
        // fixme: todo
        Ok(())
    }

    // Read the assignments between loans at a  point
    // REQUIRES: loan issues have been computed
    fn compute_loan_assigned_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) -> AnalysisResult<()> {
        // fixme: todo
        Ok(())
    }

    /// Collect the loan issue facts from Polonius
    fn compute_loan_issues<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) -> AnalysisResult<()> {
        for (issuing_origin, loan, point) in mir.input_facts.loan_issued_at.iter() {
            // Insert facts for the new borrow temporary
            Self::insert_origin_lhs_constraint(
                working_table,
                *issuing_origin,
                OriginLHS::Loan(*loan),
            );
            Self::insert_loan_issue_constraint(working_table, *point, *issuing_origin);

            // Insert facts for reborrows
            let location = Self::expect_mid_location(mir.location_table.to_location(*point));
            let statement = Self::mir_kind_at(mir, location);
            let borrowed_from_place = *Self::get_borrowed_from_place(&statement, location)?;
            if let Some(origin_borrowed_from) = working_table
                .origins
                .get_origin(OriginLHS::Place(borrowed_from_place))
            {
                Self::insert_packing_constraint(
                    working_table,
                    *point,
                    origin_borrowed_from,
                    OriginLHS::Place(borrowed_from_place),
                );
                Self::insert_structural_edge(
                    working_table,
                    *point,
                    *issuing_origin,
                    origin_borrowed_from,
                    SubsetBaseKind::Reborrow,
                );
            }
        }
        Ok(())
    }

    // Constraint: An origin has a known LHS place
    fn insert_origin_lhs_constraint(
        working_table: &mut Self,
        origin: Region,
        lhs: OriginLHS<'tcx>,
    ) {
        working_table.origins.new_constraint(origin, lhs);
    }

    // Constraint: Origin is issued a loan at a given point
    fn insert_loan_issue_constraint(working_table: &mut Self, point: PointIndex, origin: Region) {
        working_table.loan_issues.insert(point, origin);
    }

    // Constraint: An origin must be packed to certain level at a pointIndex
    fn insert_packing_constraint(
        working_table: &mut Self,
        point: PointIndex,
        origin: Region,
        packing: OriginLHS<'tcx>,
    ) {
        working_table
            .origin_packing_at
            .entry(point)
            .and_modify(|constraints| constraints.push((origin, packing)));
    }

    // Constraint: An origin must be packed to certain level at a pointIndex
    fn insert_structural_edge(
        working_table: &mut Self,
        point: PointIndex,
        origin_from: Region,
        origin_to: Region,
        kind: SubsetBaseKind,
    ) {
        working_table
            .structural_edge
            .entry(point)
            .and_modify(|constraints| constraints.push((kind, origin_from, origin_to)));
    }

    // Panics when a location is not a start location
    fn expect_mid_location(location: RichLocation) -> Location {
        match location {
            RichLocation::Start(_) => panic!("expected a start location"),
            RichLocation::Mid(l) => return l,
        };
    }

    /// Collect the MIR statement at a location, panic if not a valid location
    fn mir_kind_at<'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        location: Location,
    ) -> StatementKinds<'mir, 'tcx> {
        let stmt = mir.body.stmt_at(location);
        // fixme: can't pattern match on stmt because the Either used by rustc is private?
        if stmt.is_left() {
            return StatementKinds::Stmt(&stmt.left().unwrap().kind);
        } else {
            return StatementKinds::Term(&stmt.right().unwrap().kind);
        }
    }

    // Get the borrowed-from place in all cases where we currently support borrow creation
    fn get_borrowed_from_place<'a, 'mir>(
        stmt: &'a StatementKinds<'mir, 'tcx>,
        loc: Location,
    ) -> AnalysisResult<&'a mir::Place<'tcx>> {
        match stmt {
            StatementKinds::Stmt(StatementKind::Assign(box (
                _,
                Rvalue::Ref(
                    _,
                    BorrowKind::Mut {
                        allow_two_phase_borrow: false,
                    },
                    p,
                ),
            ))) => Ok(p),
            _ => Err(AnalysisError::UnsupportedStatement(loc)),
        }
    }

    // REQUIRES: Loan issue locations have been computed
    // Infer the reason why a subset_base fact was emitted by the compiler
    // FIXME: This is one place where the inference is limited, and this method should
    //  be updated once we have better information from the Polonius team.
    fn characterize_subset_base<'mir>(
        working_table: &mut Self,
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> AnalysisResult<()> {
        // For each collection of subset_bases partitioned by point...
        let subset_base_locations: FxHashMap<PointIndex, FxHashSet<(Region, Region)>> = mir
            .input_facts
            .subset_base
            .iter()
            .fold(FxHashMap::default(), |mut acc, (o1, o2, p)| {
                acc.entry(*p).or_default().insert((*o1, *o2));
                acc
            });

        for (point, mut set) in subset_base_locations.iter() {
            // Main inference algorithm for subset_base facts.
            // 1. Loan Issues
            if let Some(issuing_origin) = working_table.loan_issues.get(point) {
                // 1.1. There should be at most ONE subset downstream of the issuing region, for reborrows
                // 1.2. There should be exactly ONE assignment
            } else {
                // 2. All other relations should be assignments, the MIR at the point should be an assignment
                // 2.1 There should be at most ONE other relation, the assignment.
                //          Both origins should either be new, or cohere with the known origins.
            }

            if set.len() > 0 {
                panic!("Inference algoirithm terminated early");
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
enum SubsetBaseKind {
    Reborrow,
    LoanIssue,
    Move,
}
