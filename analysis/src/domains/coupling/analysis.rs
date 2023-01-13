// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

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
#[derive(Debug)]
pub struct FactTable<'tcx> {
    /// Issue of a loan, into it's issuing origin, and a loan of a place
    loan_issues: LoanIssues<'tcx>,

    // Interpretation of regions in terms of places and temporaries
    origins: OriginPlaces<'tcx>,
}

/// Issue of a new loan. The assocciated region should represent a borrow temporary.
type LoanIssues<'tcx> = FxHashMap<PointIndex, Region>;

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
        let normalized_c = Self::normalize_origin_lhs(c);
        if let Some(old_lhs) = self.0.insert(r, normalized_c.clone()) {
            assert!(old_lhs == normalized_c);
        }
    }

    fn normalize_origin_lhs(c: OriginLHS<'tcx>) -> OriginLHS<'tcx> {
        // fixme: Need to check that p is maximally packed if it is a place
        return c;
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
    pub fn new(mir: &BodyWithBorrowckFacts<'tcx>) -> AnalysisResult<Self> {
        let mut origins: OriginPlaces<'tcx> = Default::default();
        let loan_issues = Self::compute_loan_issues(mir, &mut origins)?;
        let table = Ok(Self {
            loan_issues,
            origins,
        });
        println!("[fact table]  {:#?}", table);
        return table;
    }

    /// Collect the loan issue facts from Polonius
    fn compute_loan_issues<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        origin_map: &'a mut OriginPlaces<'tcx>,
    ) -> AnalysisResult<LoanIssues<'tcx>> {
        let mut ret = FxHashMap::<_, _>::default();
        for (o, l, p) in mir.input_facts.loan_issued_at.iter() {
            // Insert facts for the borrow temporary
            origin_map.new_constraint((*o).clone(), OriginLHS::Loan((*l).clone()));
            ret.insert(*p, *o);

            // Insert facts for reborrows (fixme)
            // let location = Self::expect_mid_location(mir.location_table.to_location(*p));
            // let statement = Self::mir_kind_at(mir, location);
            // let place = (*Self::get_borrowed_from_place(&statement, location)?).clone();
        }
        return Ok(ret);
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
}
