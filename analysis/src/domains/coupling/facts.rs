// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    abstract_interpretation::AnalysisResult,
    mir_utils::{
        self, expect_mid_location, get_assigned_to_place, get_borrowed_from_place,
        get_moved_from_place, get_storage_dead, maximally_pack, mir_kind_at, Place,
    },
    AnalysisError,
};
use prusti_rustc_interface::{
    borrowck::{
        consumers::{RichLocation, RustcFacts},
        BodyWithBorrowckFacts,
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{BorrowKind, Location, Operand, Rvalue, StatementKind},
        ty::TyCtxt,
    },
    polonius_engine::FactTypes,
};
use std::collections::{BTreeMap, BTreeSet};

// These types are stolen from Prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

/// Issue of a new loan. The assocciated region should represent a borrow temporary.
pub(crate) type LoanIssues<'tcx> = FxHashMap<PointIndex, (Region, Place<'tcx>)>;
pub(crate) type OriginPacking<'tcx> = FxHashMap<PointIndex, Vec<(Region, OriginLHS<'tcx>)>>;
pub(crate) type StructuralEdge = FxHashMap<PointIndex, Vec<(SubsetBaseKind, Region, Region)>>;
pub(crate) type OriginContainsLoanAt = FxHashMap<PointIndex, BTreeMap<Region, BTreeSet<Loan>>>;
pub(crate) type LoanKilledAt = FxHashMap<PointIndex, BTreeSet<Loan>>;
pub(crate) type SubsetsAt = FxHashMap<PointIndex, BTreeMap<Region, BTreeSet<Region>>>;

/// Struct containing lookups for all the Polonius facts
pub struct FactTable<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,

    /// Issue of a loan, into it's issuing origin, and a loan of a place
    pub(crate) loan_issues: LoanIssues<'tcx>,

    /// Interpretation of regions in terms of places and temporaries
    pub(crate) origins: OriginPlaces<'tcx>,

    /// Some points requre the LHS of an origin to be repacked to include a specific place
    pub(crate) origin_packing_at: OriginPacking<'tcx>,

    /// Edges to add at each point, with interpretation
    pub(crate) structural_edge: StructuralEdge,

    /// Analouges of polonius facts
    pub(crate) origin_contains_loan_at: OriginContainsLoanAt,
    pub(crate) loan_killed_at: LoanKilledAt,
    pub(crate) subsets_at: SubsetsAt,
}

impl<'tcx> FactTable<'tcx> {
    /// Default unpopulated fact table
    fn default_from_tcx(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
            loan_issues: Default::default(),
            origins: OriginPlaces {
                map: Default::default(),
                tcx,
            },
            origin_packing_at: Default::default(),
            structural_edge: Default::default(),
            origin_contains_loan_at: Default::default(),
            loan_killed_at: Default::default(),
            subsets_at: Default::default(),
        }
    }

    /// New populated fact table
    pub fn new(mir: &BodyWithBorrowckFacts<'tcx>, tcx: TyCtxt<'tcx>) -> AnalysisResult<Self> {
        let mut working_table = Self::default_from_tcx(tcx);
        Self::compute_loan_issues(mir, &mut working_table)?;
        Self::characterize_subset_base(&mut working_table, mir)?;
        Self::collect_loan_killed_at(mir, &mut working_table);
        Self::collect_origin_contains_loan_at(mir, &mut working_table);
        Self::collect_subsets_at(mir, &mut working_table);
        println!("[fact table]  {:#?}", working_table);
        return Ok(working_table);
    }

    /// Collect all facts due to loan issues
    /// Before computation:
    ///     - Nothing needs to be known
    ///
    /// For each loan_issued_at(issuing_origin, bwx, p):
    ///     - Assert that l is a middle location
    ///     - Assert that the statement is _ = &mut borrowed_from_place;
    ///     - Constrain the LHS of issuing_origin to be bwx
    ///     - Constrain that loan bwx is a borrow from borrowed_from_place at p
    ///
    /// After computation:
    ///     - The origin associated to all loan temporaries is known
    ///     - The borrowed-from place for all loans is known
    fn compute_loan_issues<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) -> AnalysisResult<()> {
        for (issuing_origin, loan, point) in mir.input_facts.loan_issued_at.iter() {
            // Insert facts for the new borrow temporary
            let location = expect_mid_location(mir.location_table.to_location(*point));
            let statement = mir_kind_at(mir, location);
            let borrowed_from_place: mir_utils::Place<'tcx> =
                (*get_borrowed_from_place(&statement, location)?).into();

            Self::check_or_construct_origin(
                working_table,
                &mir.body as &mir::Body,
                OriginLHS::Loan(*loan),
                *issuing_origin,
            )?;
            Self::insert_loan_issue_constraint(
                working_table,
                *point,
                *issuing_origin,
                borrowed_from_place,
            );
        }
        Ok(())
    }

    /// Explain the subset_base facts
    /// Before computation:
    ///     - Issuing origins must be charaterized
    ///     - Borrowed-from places must be annotated for all borrows
    ///
    /// For each point p with a collection of subset_base facts:
    ///     - (1) if the place is a loan issue:
    ///         - (1.1) there should be exactly one base superset of the issuing_origin origin
    ///             of the form (issuing_origin, assigning_origin)
    ///             and the statement is _ = &mut assigned_from_place;
    ///     fixme (markus) finish doccumenting this
    ///
    /// After computation:
    fn characterize_subset_base<'mir>(
        working_table: &mut Self,
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
    ) -> AnalysisResult<()> {
        // Collect subset_base facts into a map indexed by points
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
                if let &[assigning_subset @ (_, assigning_origin)] = &set
                    .iter()
                    .filter(|(o, _)| *o == issuing_origin)
                    .collect::<Vec<_>>()[..]
                {
                    // Issuing borrow assignment: the new borrow is assigned into assigning_subset.1
                    let location = expect_mid_location(mir.location_table.to_location(point));
                    let statement = mir_kind_at(mir, location);
                    let assigned_to_place = *get_assigned_to_place(&statement, location)?;

                    // fixme: get something like this to work
                    // assert_eq!(
                    //     working_table
                    //         .origins
                    //         .get_origin(OriginLHS::Place(issuing_borrowed_from_place)),
                    //     Some(*assigned_from_origin)
                    // );
                    Self::insert_structural_edge(
                        working_table,
                        point,
                        issuing_origin,
                        *assigning_origin,
                        SubsetBaseKind::LoanIssue,
                    );
                    // fixme: Self::insert_origin_lhs_constraint(working_table, mir, origin, packing.clone());
                    Self::insert_packing_constraint(
                        working_table,
                        point,
                        *assigning_origin,
                        OriginLHS::Place(assigned_to_place.into()),
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
                    let location = expect_mid_location(mir.location_table.to_location(point));
                    let statement = mir_kind_at(mir, location);
                    let borrowed_from_place: OriginLHS<'tcx> =
                        OriginLHS::Place((*get_borrowed_from_place(&statement, location)?).into());

                    // If the reborrowed-from place is None, it doesn't mean that it's a borrow of owned data!
                    // We might just be constructing the fact table out of order
                    Self::check_or_construct_origin(
                        working_table,
                        &mir.body,
                        borrowed_from_place.clone(),
                        *reborrowing_origin,
                    )?;

                    // fixme: Self::insert_origin_lhs_constraint(working_table, mir, origin, packing.clone());
                    Self::insert_packing_constraint(
                        working_table,
                        point,
                        *reborrowing_origin,
                        borrowed_from_place,
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

                let location = expect_mid_location(mir.location_table.to_location(point));
                let statement = mir_kind_at(mir, location);
                let t_to: AnalysisResult<mir_utils::Place> =
                    get_assigned_to_place(&statement, location);
                let t_from: AnalysisResult<mir_utils::Place> =
                    get_moved_from_place(&statement, location);
                if let (Ok(assigned_to_place), Ok(assigned_from_place)) = (t_to, t_from) {
                    if let &[assigning_subset @ (assigned_from_origin, assigned_to_origin)] =
                        &set.iter().collect::<Vec<_>>()[..]
                    {
                        let to_place: OriginLHS<'tcx> =
                            OriginLHS::Place((*assigned_to_place).into());
                        let from_place: OriginLHS<'tcx> =
                            OriginLHS::Place((*assigned_from_place).into());

                        Self::check_or_construct_origin(
                            working_table,
                            &mir.body,
                            from_place.clone(),
                            *assigned_from_origin,
                        )?;
                        Self::check_or_construct_origin(
                            working_table,
                            &mir.body,
                            to_place.clone(),
                            *assigned_to_origin,
                        )?;

                        // fixme: Self::insert_origin_lhs_constraint(working_table, mir, origin, packing.clone());
                        Self::insert_packing_constraint(
                            working_table,
                            point,
                            *assigned_to_origin,
                            to_place,
                        );

                        // fixme: Self::insert_origin_lhs_constraint(working_table, mir, origin, packing.clone());
                        Self::insert_packing_constraint(
                            working_table,
                            point,
                            *assigned_from_origin,
                            from_place,
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

    /// Promote Polonius facts: Workaround for memory safety
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

    /// Promote Polonius facts: Workaround for memory safety
    fn collect_subsets_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) {
        for (l, m) in mir.output_facts.subset.iter() {
            working_table.subsets_at.insert(*l, (*m).to_owned());
        }
    }

    /// Promote Polonius facts: Workaround for memory safety
    fn collect_loan_killed_at<'a, 'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        working_table: &'a mut Self,
    ) {
        for (l, p) in mir.input_facts.loan_killed_at.iter() {
            let loan_set = working_table.loan_killed_at.entry(*p).or_default();
            loan_set.insert(l.to_owned());
        }
    }

    /// Constrain an origin to have a particular LHS, or panic if the constraint conflicts with
    /// an existing origin.
    /// Model: All origins must have a unique cannonical LHS.
    fn check_or_construct_origin<'mir>(
        working_table: &mut Self,
        mir: &mir::Body<'tcx>,
        lhs: OriginLHS<'tcx>,
        origin: Region,
    ) -> AnalysisResult<()> {
        if let Some(real_origin) = working_table.origins.get_origin(mir, lhs.to_owned()) {
            assert_eq!(real_origin, origin);
        } else {
            working_table.origins.new_constraint(mir, origin, lhs);
        }
        Ok(())
    }

    /// Access the origins refered to by the origin_contains_loan_at fact at a point
    /// Model: In calculating at p, all origins_at(p) must be given a signature
    pub fn origins_at(&self, p: &PointIndex) -> AnalysisResult<BTreeSet<Region>> {
        match self.origin_contains_loan_at.get(p) {
            None => panic!("accessing location outside MIR"),
            Some(s) => Ok(s.keys().cloned().collect::<_>()),
        }
    }

    /// Get the storage_dead facts at a location
    /// Model: All get_storage_dead_at(_, p) must be killed between p and successor(p).
    /// Model: Places are only killed between Start and Mid locations
    pub fn get_storage_dead_at<'mir>(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        location: PointIndex,
    ) -> Option<Place<'tcx>>
    where
        'tcx: 'mir,
    {
        let rich_location = mir.location_table.to_location(location);
        match rich_location {
            RichLocation::Start(loc) => get_storage_dead(&mir_kind_at(mir, loc), loc),
            RichLocation::Mid(_) => None,
        }
    }

    /// Get the subsets associated with a move at each point
    /// Model: For each (from, to) subset, from is is a subset of to, and to is killed.
    pub fn get_move_origins_at(&self, location: &PointIndex) -> Vec<(Region, Region)> {
        match self.structural_edge.get(location) {
            Some(v) => v
                .iter()
                .filter(|(kind, _, _)| {
                    (*kind == SubsetBaseKind::Move) || (*kind == SubsetBaseKind::LoanIssue)
                })
                .map(|(_, from, to)| (*from, *to))
                .collect::<_>(),
            None => Vec::default(),
        }
    }

    /// Add a loan_issue constraint to the table
    fn insert_loan_issue_constraint(
        working_table: &mut Self,
        point: PointIndex,
        origin: Region,
        borrowed_from_place: Place<'tcx>,
    ) {
        working_table
            .loan_issues
            .insert(point, (origin, borrowed_from_place));
    }

    /// Constrain an origin to be repacked in to include (not equal) a set of permissions at a point
    fn insert_packing_constraint(
        working_table: &mut Self,
        point: PointIndex,
        origin: Region,
        packing: OriginLHS<'tcx>,
    ) {
        let constraints = working_table.origin_packing_at.entry(point).or_default();
        constraints.push((origin, packing));
    }

    /// Add a subset constraint between origins, which has been explained
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
}

impl<'tcx> std::fmt::Debug for FactTable<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FactTable")
            .field("loan_issues", &self.loan_issues)
            .field("origins", &self.origins)
            .field("origin_packing_at", &self.origin_packing_at)
            .field("structural_edge", &self.structural_edge)
            .field("origin_contains_loan_at", &self.origin_contains_loan_at)
            .field("loan_killed_at", &self.loan_killed_at)
            .field("subsets_at", &self.subsets_at)
            .finish()
    }
}

/// Cannonical permissions associated with an origin
/// Precise relationship between these two are yet unconfirmed by the Polonius team
pub(crate) struct OriginPlaces<'tcx> {
    pub(crate) map: FxHashMap<Region, OriginLHS<'tcx>>,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> OriginPlaces<'tcx> {
    /// Attempt to add a new constraint to the origin mapping
    /// Panic if the constraint conflicts with an existing constraint
    pub fn new_constraint(&mut self, mir: &mir::Body<'tcx>, r: Region, c: OriginLHS<'tcx>) {
        let normalized_c = self.normalize_origin_lhs(mir, c);
        if let Some(old_lhs) = self.map.insert(r, normalized_c.clone()) {
            assert_eq!(
                old_lhs, normalized_c,
                "[failure] new OriginPlaces constratint normalization: {:?} /= {:?}",
                old_lhs, normalized_c
            );
        }
    }

    /// Rewrite c into a cannonical form for key equality
    /// eg. normalize_origin_lhs(unpack(x)) == normalize_origin_lhs(x)
    /// fixme: this is currently broken
    fn normalize_origin_lhs(&self, mir: &mir::Body<'tcx>, c: OriginLHS<'tcx>) -> OriginLHS<'tcx> {
        match c {
            OriginLHS::Place(p) => {
                let p1 = maximally_pack(mir, self.tcx, p);
                println!(
                    "[debug] normalizing {:?} into {:?}",
                    c,
                    OriginLHS::Place(p1)
                );
                OriginLHS::Place(p1)
            }
            OriginLHS::Loan(_) => {
                println!("[debug] normalizing {:?} into {:?}", c, c);
                c
            }
        }
    }

    /// Attempt to obtain the origin associated with an OriginLHS
    /// This fails with None if no origin exists
    pub fn get_origin(&self, mir: &mir::Body<'tcx>, c: OriginLHS<'tcx>) -> Option<Region> {
        let normalized_c = self.normalize_origin_lhs(mir, c);
        self.map
            .iter()
            .find(|(_, v)| **v == normalized_c)
            .map(|(k, _)| *k)
    }
}

impl<'tcx> std::fmt::Debug for OriginPlaces<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:#?}", self.map))
    }
}

/// Model: Possible interpretations of an origin as permissions
///     Every origin is either:
///         - A temporary value associated with a loan
///         - A maximally packed (canonical) place
#[derive(PartialEq, Eq, Clone)]
pub enum OriginLHS<'tcx> {
    Place(Place<'tcx>),
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

/// Model: Possible interpretations of a SubsetBase fact
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum SubsetBaseKind {
    Reborrow,
    LoanIssue,
    Move,
}
