// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{BTreeMap, BTreeSet};

use super::state::{Loan, PointIndex, Region};
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
        mir::{BorrowKind, Location, Operand, Rvalue, StatementKind, TerminatorKind},
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
#[derive(Debug)]
pub struct FactTable<'tcx> {
    /// Issue of a loan, into it's issuing origin, and a loan of a place
    pub(crate) loan_issues: LoanIssues<'tcx>,

    // Interpretation of regions in terms of places and temporaries
    pub(crate) origins: OriginPlaces<'tcx>,

    // Some points requre the LHS of an origin to be repacked to include a specific place
    pub(crate) origin_packing_at: OriginPacking<'tcx>,

    // Edges to add at each point, with interpretation
    pub(crate) structural_edge: StructuralEdge,

    // straight analouges of polonius facts
    pub(crate) origin_contains_loan_at: OriginContainsLoanAt,
    pub(crate) loan_killed_at: LoanKilledAt,
}

/// Issue of a new loan. The assocciated region should represent a borrow temporary.
pub(crate) type LoanIssues<'tcx> = FxHashMap<PointIndex, (Region, mir::Place<'tcx>)>;
pub(crate) type OriginPacking<'tcx> = FxHashMap<PointIndex, Vec<(Region, OriginLHS<'tcx>)>>;
pub(crate) type StructuralEdge = FxHashMap<PointIndex, Vec<(SubsetBaseKind, Region, Region)>>;
pub(crate) type OriginContainsLoanAt = FxHashMap<PointIndex, BTreeMap<Region, BTreeSet<Loan>>>;
pub(crate) type LoanKilledAt = FxHashMap<PointIndex, BTreeSet<Loan>>;

/// Assignment between Origins and places
/// Precise relationship between these two are yet unconfirmed by the Polonius team
/// NOTE: The LHS of a origin is no necessarily this place, as it may be further unpacked.
/// NOTE: We don't know if this is a bijection yet, nor the full scope of Temporaries Polonius
/// uses (see: OriginLHS struct for the current characterization)
pub(crate) struct OriginPlaces<'tcx> {
    map: FxHashMap<Region, OriginLHS<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> std::fmt::Debug for OriginPlaces<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:#?}", self.map))
    }
}

impl<'tcx> OriginPlaces<'tcx> {
    // Attempt to add a new constraint to the origin mapping
    pub fn new_constraint(&mut self, r: Region, c: OriginLHS<'tcx>) {
        let normalized_c = self.normalize_origin_lhs(c);
        if let Some(old_lhs) = self.map.insert(r, normalized_c.clone()) {
            assert!(old_lhs == normalized_c);
        }
    }

    // todo: remove this code from prusti-pcs
    // and move to common library
    fn strip_place(&self, place: mir::Place<'tcx>) -> Option<mir::Place<'tcx>> {
        let mut projection = place.projection.to_vec();
        projection.pop()?;
        Some(mir::Place {
            local: place.local,
            projection: self.tcx.intern_place_elems(&projection),
        })
    }

    /// Rewrite c into a cannonical form for key equality
    /// eg. normalize_origin_lhs(*x) == normalize_origin_lhs(x)
    fn normalize_origin_lhs(&self, c: OriginLHS<'tcx>) -> OriginLHS<'tcx> {
        // fixme: Need to check that p is maximally packed if it is a place
        match c {
            OriginLHS::Place(p) => match self.strip_place(p) {
                Some(p1) => OriginLHS::Place(p1),
                None => OriginLHS::Place(p),
            },
            OriginLHS::Loan(_) => c,
        }
    }

    fn get_origin(&self, c: OriginLHS<'tcx>) -> Option<Region> {
        let normalized_c = self.normalize_origin_lhs(c);
        self.map
            .iter()
            .find(|(_, v)| **v == normalized_c)
            .map(|(k, _)| *k)
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

#[derive(Debug)]
pub(crate) enum SubsetBaseKind {
    Reborrow,
    LoanIssue,
    Move,
}

enum StatementKinds<'mir, 'tcx: 'mir> {
    Stmt(&'mir StatementKind<'tcx>),
    Term(&'mir TerminatorKind<'tcx>),
}

impl<'tcx> FactTable<'tcx> {
    fn default_from_tcx(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            loan_issues: Default::default(),
            origins: OriginPlaces {
                map: Default::default(),
                tcx,
            },
            origin_packing_at: Default::default(),
            structural_edge: Default::default(),
            origin_contains_loan_at: Default::default(),
            loan_killed_at: Default::default(),
        }
    }

    pub fn new(mir: &BodyWithBorrowckFacts<'tcx>, tcx: TyCtxt<'tcx>) -> AnalysisResult<Self> {
        let mut working_table = Self::default_from_tcx(tcx);
        Self::compute_loan_issues(mir, &mut working_table)?;
        Self::characterize_subset_base(&mut working_table, mir)?;
        Self::collect_loan_killed_at(mir, &mut working_table);
        Self::collect_origin_contains_loan_at(mir, &mut working_table);
        println!("[fact table]  {:#?}", working_table);
        return Ok(working_table);
    }

    /// Access the origins refered to by the origin_contains_loan_at fact at a point
    pub fn origins_at(&self, p: &PointIndex) -> AnalysisResult<BTreeSet<Region>> {
        match self.origin_contains_loan_at.get(p) {
            None => panic!("accessing location outside MIR"),
            Some(s) => Ok(s.keys().cloned().collect::<_>()),
        }
    }

    /// Workaround for memory safety
    fn collect_origin_contains_loan_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) {
        for (k, v) in mir.output_facts.origin_contains_loan_at.iter() {
            working_table
                .origin_contains_loan_at
                .insert(*k, (*v).to_owned());
        }
    }

    /// Workaround for memory safety
    fn collect_loan_killed_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) {
        for (l, p) in mir.input_facts.loan_killed_at.iter() {
            let loan_set = working_table.loan_killed_at.entry(*p).or_default();
            loan_set.insert(l.to_owned());
        }
    }

    /// Collect the loan issue facts from Polonius
    fn compute_loan_issues<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) -> AnalysisResult<()> {
        for (issuing_origin, loan, point) in mir.input_facts.loan_issued_at.iter() {
            // Insert facts for the new borrow temporary
            let location = Self::expect_mid_location(mir.location_table.to_location(*point));
            let statement = Self::mir_kind_at(mir, location);
            let borrowed_from_place = *Self::get_borrowed_from_place(&statement, location)?;
            Self::insert_origin_lhs_constraint(
                working_table,
                *issuing_origin,
                OriginLHS::Loan(*loan),
            );
            Self::insert_loan_issue_constraint(
                working_table,
                *point,
                *issuing_origin,
                borrowed_from_place,
            );
        }
        Ok(())
    }

    // Constraint: An origin has a known LHS place
    // Location insensitive, should panic if an origin has two known places
    fn insert_origin_lhs_constraint(
        working_table: &mut Self,
        origin: Region,
        lhs: OriginLHS<'tcx>,
    ) {
        working_table.origins.new_constraint(origin, lhs);
    }

    // Constraint: Origin is issued a loan at a given point
    fn insert_loan_issue_constraint(
        working_table: &mut Self,
        point: PointIndex,
        origin: Region,
        borrowed_from_place: mir::Place<'tcx>,
    ) {
        working_table
            .loan_issues
            .insert(point, (origin, borrowed_from_place));
    }

    // Constraint: An origin must be packed to certain level at a pointIndex
    // Implicitly, the LHS should cohere with the existing LHS.
    fn insert_packing_constraint(
        working_table: &mut Self,
        point: PointIndex,
        origin: Region,
        packing: OriginLHS<'tcx>,
    ) {
        Self::insert_origin_lhs_constraint(working_table, origin, packing.clone());
        working_table
            .origin_packing_at
            .entry(point)
            .and_modify(|constraints| constraints.push((origin, packing)));
    }

    // Constraint: An edge between origins
    fn insert_structural_edge(
        working_table: &mut Self,
        point: PointIndex,
        origin_from: Region,
        origin_to: Region,
        kind: SubsetBaseKind,
    ) {
        let constraint_set = working_table.structural_edge.entry(point).or_default();
        constraint_set.push((kind, origin_from, origin_to));
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

    // Get the assigned-to place in all cases where we currently support borrow assignment
    fn get_assigned_to_place<'a, 'mir>(
        stmt: &'a StatementKinds<'mir, 'tcx>,
        loc: Location,
    ) -> AnalysisResult<&'a mir::Place<'tcx>> {
        match stmt {
            StatementKinds::Stmt(StatementKind::Assign(box (p, _))) => Ok(p),
            _ => Err(AnalysisError::UnsupportedStatement(loc)),
        }
    }

    // Get the assigned-to place in all cases where we currently support borrow assignment
    fn get_moved_from_place<'a, 'mir>(
        stmt: &'a StatementKinds<'mir, 'tcx>,
        loc: Location,
    ) -> AnalysisResult<&'a mir::Place<'tcx>> {
        match stmt {
            StatementKinds::Stmt(StatementKind::Assign(box (_, Rvalue::Use(Operand::Move(p))))) => {
                Ok(p)
            }
            _ => Err(AnalysisError::UnsupportedStatement(loc)),
        }
    }

    fn check_or_construct_origin<'mir>(
        working_table: &mut Self,
        lhs: OriginLHS<'tcx>,
        origin: Region,
    ) -> AnalysisResult<()> {
        if let Some(real_origin) = working_table.origins.get_origin(lhs.to_owned()) {
            assert_eq!(real_origin, origin);
        } else {
            Self::insert_origin_lhs_constraint(working_table, origin, lhs)
        }
        Ok(())
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

        for (point, s) in subset_base_locations.into_iter() {
            let mut set = s.clone();
            if let Some((issuing_origin, issuing_borrowed_from_place)) = working_table
                .loan_issues
                .get(&point)
                .map(|(o, p)| (*o, *p).clone())
            {
                // 1.1. There should be at EXACTLY ONE subset upstream of the issuing origin
                if let &[assigning_subset @ (assigned_from_origin, assigning_origin)] = &set
                    .iter()
                    .filter(|(o, _)| *o == issuing_origin)
                    .collect::<Vec<_>>()[..]
                {
                    // Issuing borrow assignment: the new borrow is assigned into assigning_subset.1
                    let location = Self::expect_mid_location(mir.location_table.to_location(point));
                    let statement = Self::mir_kind_at(mir, location);
                    let assigned_to_place = *Self::get_assigned_to_place(&statement, location)?;
                    assert_eq!(
                        working_table
                            .origins
                            .get_origin(OriginLHS::Place(issuing_borrowed_from_place)),
                        Some(*assigned_from_origin)
                    );
                    Self::insert_structural_edge(
                        working_table,
                        point,
                        issuing_origin,
                        *assigning_origin,
                        SubsetBaseKind::LoanIssue,
                    );
                    Self::insert_packing_constraint(
                        working_table,
                        point,
                        *assigning_origin,
                        OriginLHS::Place(assigned_to_place),
                    );
                    set.remove(&assigning_subset.clone());
                } else {
                    panic!("impossible: issued borrow without corresponding assignment");
                }

                // 1.2. There should be AT MOST ONE reborrowed origin
                if let &[reborrowing_subset @ (reborrowing_origin, _)] = &set
                    .iter()
                    .filter(|(_, o)| *o == issuing_origin)
                    .collect::<Vec<_>>()[..]
                {
                    let location = Self::expect_mid_location(mir.location_table.to_location(point));
                    let statement = Self::mir_kind_at(mir, location);
                    let borrowed_from_place = *Self::get_borrowed_from_place(&statement, location)?;
                    // If the reborrowed-from place is None, it doesn't mean that it's a borrow of owned data!
                    // We might just be constructing the fact table out of order
                    Self::check_or_construct_origin(
                        working_table,
                        OriginLHS::Place(borrowed_from_place),
                        *reborrowing_origin,
                    )?;
                    Self::insert_packing_constraint(
                        working_table,
                        point,
                        *reborrowing_origin,
                        OriginLHS::Place(borrowed_from_place),
                    );
                    Self::insert_structural_edge(
                        working_table,
                        point,
                        issuing_origin,
                        *reborrowing_origin,
                        SubsetBaseKind::Reborrow,
                    );

                    // Reborrow repacking should be handled by the loan analysis
                    set.remove(&reborrowing_subset.clone());
                }
            } else {
                // 2. All other relations should be assignments not between issuing origins
                //      If there is exactly one subset AND The mir is an assignment
                // 2.1 There should be at most ONE other relation, the assignment.
                //          Both origins should either be new, or cohere with the known origins.
                // Also add kills due to assignments here

                let location = Self::expect_mid_location(mir.location_table.to_location(point));
                let statement = Self::mir_kind_at(mir, location);
                let t_to = Self::get_assigned_to_place(&statement, location);
                let t_from = Self::get_moved_from_place(&statement, location);
                if let (Ok(assigned_to_place), Ok(assigned_from_place)) = (t_to, t_from) {
                    if let &[assigning_subset @ (assigned_from_origin, assigned_to_origin)] =
                        &set.iter().collect::<Vec<_>>()[..]
                    {
                        Self::check_or_construct_origin(
                            working_table,
                            OriginLHS::Place(*assigned_from_place),
                            *assigned_from_origin,
                        )?;
                        Self::check_or_construct_origin(
                            working_table,
                            OriginLHS::Place(*assigned_to_place),
                            *assigned_to_origin,
                        )?;
                        Self::insert_packing_constraint(
                            working_table,
                            point,
                            *assigned_to_origin,
                            OriginLHS::Place(*assigned_to_place),
                        );
                        Self::insert_packing_constraint(
                            working_table,
                            point,
                            *assigned_from_origin,
                            OriginLHS::Place(*assigned_from_place),
                        );
                        Self::insert_structural_edge(
                            working_table,
                            point,
                            *assigned_from_origin,
                            *assigned_to_origin,
                            SubsetBaseKind::Move,
                        );
                        set.remove(&assigning_subset.clone());
                    } else {
                        panic!("unhandled case in inference algorithm");
                    }
                }
            }

            if set.len() > 0 {
                panic!("Inference algoirithm terminated early");
            }
        }
        Ok(())
    }
}
