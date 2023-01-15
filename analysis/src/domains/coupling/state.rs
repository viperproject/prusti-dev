// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use log::info;
use crate::{
    abstract_interpretation::{AbstractState, AnalysisResult},
    mir_utils::Place,
};
use prusti_rustc_interface::{
    borrowck::{
        consumers::{RichLocation, RustcFacts},
        BodyWithBorrowckFacts,
    },
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{
        mir,
        mir::{Location, TerminatorKind},
    },
    polonius_engine::FactTypes,
};
use serde::{ser::SerializeStruct, Serialize, Serializer};
use std::{collections::BTreeSet, fmt, rc::Rc};

use super::FactTable;

// These types are stolen from prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct Tagged<Data, Tag> {
    data: Data,
    tag: Option<Tag>,
}

impl<Data, Tag> Tagged<Data, Tag> {
    // Tag a place if it is not already tagged
    fn tag(&mut self, t: Tag) {
        if self.tag.is_none() {
            self.tag = Some(t);
        }
    }
}

/// Nodes for the coupling digraph
#[derive(Clone, PartialEq, Eq)]
pub enum CDGNode<'tcx> {
    Place(Tagged<Place<'tcx>, Location>),
    Borrow(Tagged<Loan, Location>),
}

impl<'tcx> CDGNode<'tcx> {
    // Kills a node, if it isn't already unkilled
    pub fn kill(&mut self, l: Location) {
        match self {
            CDGNode::Place(p) => p.tag(l),
            CDGNode::Borrow(b) => b.tag(l),
        }
    }
}

/// Corresponds to the annotations we store in the CDG
#[derive(Clone, PartialEq, Eq)]
pub enum CDGEdgeKind {
    Reborrow,
}

// Coupling graph hyper-edges
#[derive(Clone, PartialEq, Eq)]
pub struct CDGEdge<'tcx> {
    pub lhs: BTreeSet<Rc<CDGNode<'tcx>>>,
    pub rhs: BTreeSet<Rc<CDGNode<'tcx>>>,
    pub edge: CDGEdgeKind,
}

/// The CDG graph fragments associated with an origin
/// INVARIANT: Can be (roughly) interpreted as the Hoare triple
///     {leaves} edges {roots}
#[derive(Clone, PartialEq, Eq, Default)]
pub struct CDGOrigin<'tcx> {
    edges: BTreeSet<CDGEdge<'tcx>>,
    leaves: BTreeSet<Rc<CDGNode<'tcx>>>,
    roots: BTreeSet<Rc<CDGNode<'tcx>>>,
}

// A coupling graph
#[derive(Clone, Default, PartialEq, Eq)]
pub struct CDG<'tcx> {
    pub origins: FxHashMap<Region, CDGOrigin<'tcx>>,
    pub subset_invariant: bool,
    pub origin_contains_loan_at_invariant: bool,
}

#[derive(Clone)]
pub struct CouplingState<'facts, 'mir: 'facts, 'tcx: 'mir> {
    pub coupling_graph: CDG<'tcx>,
    // Also include: invariant checks, loan kill marks
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
    fact_table: &'facts FactTable<'tcx>,
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> CouplingState<'facts, 'mir, 'tcx> {
    pub(crate) fn new_empty(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        fact_table: &'facts FactTable<'tcx>,
    ) -> Self {
        Self {
            coupling_graph: Default::default(),
            fact_table,
            mir,
        }
    }

    pub(crate) fn apply_terminator_effect(
        &self,
        location: Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self)>> {
        // todo: We can't apply cdg inference at terminators without muability.
        let mut new_state = self.clone();
        new_state.apply_cdg_inference(location)?;
        let terminator = self.mir.body[location.block].terminator();
        Ok(terminator
            // todo: this can be replaced with happy_path_successors provided that the other parts of the analysis crate stop complaining
            .successors()
            .into_iter()
            .map(|bb| (bb, new_state.clone()))
            .collect())
    }

    pub(crate) fn apply_statement_effect(&mut self, location: Location) -> AnalysisResult<()> {
        self.apply_cdg_inference(location)
    }

    /// Apply the Polonius effects at a Location
    /// it is unclear to me if polonius inference is supposed to be different for Start and Mid locations yet
    fn apply_cdg_inference(&mut self, location: Location) -> AnalysisResult<()> {
        // println!("[inference]   enter {:?}", RichLocation::Start(location));
        self.apply_polonius_inference(&self.mir.location_table.start_index(location))?;
        // println!("[inference]   enter {:?}", RichLocation::Mid(location));
        self.apply_polonius_inference(&self.mir.location_table.mid_index(location))?;
        Ok(())
    }

    /// The main interpretation of Polonius facts
    fn apply_polonius_inference(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        self.apply_marked_kills()?;
        self.apply_origins(location)?;
        self.apply_packing_requirements()?;
        self.apply_loan_issues(location)?;
        self.apply_loan_moves()?;
        self.check_subset_invariant()?;
        self.check_origin_contains_loan_at_invariant()?;
        self.mark_kills()?;
        Ok(())
    }

    /// Repack the LHS of an origin to contain some place, and add edges to
    /// RHS's as appropriate to ensure connectivity.
    fn apply_packing_requirements(&mut self) -> AnalysisResult<()> {
        // fixme: implement
        Ok(())
    }

    /// For every loan which is marked as killed, kill it and remove the kill mark.
    fn apply_marked_kills(&mut self) -> AnalysisResult<()> {
        // fixme: implement
        Ok(())
    }

    /// Expire non-live origins, and add new live origins
    fn apply_origins(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        // Get the set of origins at a point from the origin_contains_loan_at fact
        // (expiries) Remove all origins which are not in that set
        //      todo: calculate and log the FPCS effects at this point
        // (issues) Include empty origins for each new origin
        Ok(())
    }

    /// Issue all new borrow temporaries into their appropriate loans, if they exist.
    fn apply_loan_issues(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        if let Some((issuing_origin, borrowed_from_place)) =
            self.fact_table.loan_issues.get(location)
        {
            // Issuing origin should be empty
            // Issuing origin LHS should be a borrow
            // Check for reborrows:
            //      If there is a reborrow, it should be the case that the borrowed_from_place
            //      is equal to the LHS of the borrowed_from_origin (ie. packing) due to the issued packing constraints.
            //      Add an edge between the two.
        }
        Ok(())
    }

    /// For every loan move:
    ///     - Kill the RHS of the move, unless it's a borrow
    ///     - Unpack the RHS to meet the packing requirement
    fn apply_loan_moves(&mut self) -> AnalysisResult<()> {
        // fixme: implement
        Ok(())
    }

    /// For every loan_killed_at at this location, mark the killed place
    fn mark_kills(&mut self) -> AnalysisResult<()> {
        // fixme: implement
        Ok(())
    }

    /// Check that every subset at a location is true.
    ///     subset(#a, #b) means the edge #b is an ancestor of the edge #a
    fn check_subset_invariant(&mut self) -> AnalysisResult<()> {
        // fixme: implement
        Ok(())
    }

    /// Check that every subset at a location is true.
    ///     origin_contains_loan_at(#a, bwx) means the temporary place bwx is
    ///     a child of #a
    fn check_origin_contains_loan_at_invariant(&mut self) -> AnalysisResult<()> {
        // fixme: implement
        Ok(())
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> Serialize for CouplingState<'facts, 'mir, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut s = serializer.serialize_struct("CouplingState", 1)?;
        s.serialize_field("fixme", "fixme")?;
        s.end()
    }
}

impl fmt::Debug for CouplingState<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CDG (fixme) {}",
            serde_json::to_string_pretty(&self).unwrap()
        )
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> PartialEq for CouplingState<'facts, 'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.coupling_graph == other.coupling_graph
    }
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> Eq for CouplingState<'facts, 'mir, 'tcx> {}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> AbstractState for CouplingState<'facts, 'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        // todo: remove stub
        false
    }

    fn join(&mut self, other: &Self) {
        // todo: remove stub
    }

    fn widen(&mut self, previous: &Self) {
        unimplemented!()
    }
}
