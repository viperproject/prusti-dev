// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use log::info;

use crate::{
    abstract_interpretation::{AbstractState, AnalysisResult, OriginLHS},
    mir_utils::{self, is_prefix, PlaceImpl},
};
use prusti_rustc_interface::{
    borrowck::{consumers::RustcFacts, BodyWithBorrowckFacts},
    middle::{mir, mir::Location, ty::TyCtxt},
    polonius_engine::FactTypes,
};
use serde::{
    ser::{SerializeMap, SerializeStruct},
    Serialize, Serializer,
};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    fmt,
    iter::zip,
    mem,
};

use super::FactTable;

// These types are stolen from prusti interface
pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

#[derive(PartialEq, Eq, Hash, Clone, PartialOrd, Ord, Debug)]
pub struct Tagged<Data, Tag> {
    pub data: Data,
    pub tag: Option<Tag>,
}

impl<Data, Tag> Tagged<Data, Tag> {
    // Tag a place if it is not already tagged
    fn tag(&mut self, t: Tag) {
        if self.tag.is_none() {
            self.tag = Some(t);
        }
    }

    fn untagged(data: Data) -> Self {
        Self { data, tag: None }
    }
}

#[derive(PartialEq, Eq, Clone, Hash)]
pub struct CPlace<'tcx> {
    pub place: mir::Place<'tcx>,
}

impl<'tcx> fmt::Debug for CPlace<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.place.fmt(f)
    }
}

impl<'tcx> CPlace<'tcx> {
    pub fn cmp_local(&self, x: &CPlace<'tcx>) -> bool {
        self.place.local == x.place.local
    }

    /// Measure the lexicographic similarity between two place's projections
    pub fn cmp_lex(&self, x: &CPlace<'tcx>) -> u32 {
        let mut r: u32 = 0;
        for (p0, p1) in zip(self.place.iter_projections(), x.place.iter_projections()) {
            if p0 != p1 {
                break;
            }
            r += 1;
        }
        return r;
    }

    pub fn unpack(&self, mir: &mir::Body<'tcx>, tcx: TyCtxt<'tcx>) -> BTreeSet<Self> {
        mir_utils::expand_struct_place(self.place, mir, tcx, None)
            .iter()
            .map(|p| Self { place: *p })
            .collect()
    }
}

impl<'tcx> PartialOrd for CPlace<'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'tcx> Ord for CPlace<'tcx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.place.local.cmp(&other.place.local) {
            Ordering::Equal => self.place.projection.cmp(other.place.projection),
            r @ (Ordering::Less | Ordering::Greater) => r,
        }
    }
}

/// Nodes for the coupling digraph
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CDGNode<'tcx> {
    Place(Tagged<CPlace<'tcx>, PointIndex>),
    Borrow(Tagged<Loan, PointIndex>),
}

impl<'tcx> fmt::Debug for CDGNode<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CDGNode::Place(tp) => {
                if let Some(tag) = tp.tag {
                    write!(f, "{:?}@{:?}", tp.data, tag)
                } else {
                    write!(f, "{:?}", tp.data)
                }
            }
            CDGNode::Borrow(tb) => {
                if let Some(tag) = tb.tag {
                    write!(f, "{:?}@{:?}", tb.data, tag)
                } else {
                    write!(f, "{:?}", tb.data)
                }
            }
        }
    }
}

impl<'tcx> CDGNode<'tcx> {
    // Kills a node, if it isn't already unkilled
    pub fn kill(mut self, l: PointIndex) -> Self {
        match &mut self {
            CDGNode::Place(p) => p.tag(l),
            CDGNode::Borrow(b) => b.tag(l),
        }
        self
    }
}

/// Corresponds to the annotations we store in the CDG
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum CDGEdgeKind {
    Borrow,
    Reborrow,
}

// Coupling graph hyper-edges
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug)]
pub struct CDGEdge<'tcx> {
    pub lhs: BTreeSet<CDGNode<'tcx>>,
    pub rhs: BTreeSet<CDGNode<'tcx>>,
    pub edge: CDGEdgeKind,
}

impl<'tcx> CDGEdge<'tcx> {
    pub fn loan_edge(loan: Loan, place: mir::Place<'tcx>) -> Self {
        Self {
            lhs: BTreeSet::from_iter([CDGNode::Borrow(Tagged::untagged(loan))].into_iter()),
            rhs: BTreeSet::from_iter(
                [CDGNode::Place(Tagged::untagged(CPlace { place }))].into_iter(),
            ),
            edge: CDGEdgeKind::Borrow,
        }
    }
}

/// The CDG graph fragments associated with an origin
/// INVARIANT: Can be (roughly) interpreted as the Hoare triple
///     {leaves} edges {roots}
#[derive(Clone, Default, PartialEq, Eq)]
pub struct CDGOrigin<'tcx> {
    edges: BTreeSet<CDGEdge<'tcx>>,
    leaves: BTreeSet<CDGNode<'tcx>>,
    roots: BTreeSet<CDGNode<'tcx>>,
}

impl<'tcx> fmt::Debug for CDGOrigin<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?} --* {:?}: ",
            self.leaves.iter().collect::<Vec<_>>(),
            self.roots.iter().collect::<Vec<_>>()
        )?;
        for e in self.edges.iter() {
            write!(
                f,
                "{:?} -{:?}-> {:?}; ",
                e.lhs.iter().collect::<Vec<_>>(),
                e.edge,
                e.rhs.iter().collect::<Vec<_>>()
            )?;
        }
        Ok(())
    }
}

impl<'tcx> CDGOrigin<'tcx> {
    pub fn is_empty(&self) -> bool {
        self.edges.is_empty() && self.leaves.is_empty() && self.leaves.is_empty()
    }

    pub fn insert_edge(&mut self, edge: CDGEdge<'tcx>) {
        // fixme: stop outselves from making bad graphs (cyclic)
        for node in edge.lhs.iter() {
            self.roots.remove(node);
            self.leaves.insert(node.clone());
        }
        for node in edge.rhs.iter() {
            self.leaves.remove(node);
            self.roots.insert(node.clone());
        }
        self.edges.insert(edge);
    }

    /// Replace a node in a BTreeSet
    fn btree_replace<T: Ord>(btree: &mut BTreeSet<T>, from: &T, to: T) {
        if btree.remove(from) {
            btree.insert(to);
        }
    }

    /// Tags all untagged places which have to_tag as a prefix in a set of nodes
    fn tag_in_set(
        set: &mut BTreeSet<CDGNode<'tcx>>,
        location: PointIndex,
        to_tag: mir::Place<'tcx>,
    ) {
        let mut to_replace: Vec<CDGNode<'tcx>> = vec![];
        for node in set.iter() {
            if let CDGNode::Place(p) = node {
                if is_prefix(
                    PlaceImpl::from_mir_place(p.data.place),
                    PlaceImpl::from_mir_place(to_tag),
                ) {
                    to_replace.push((*node).clone())
                }
            }
        }
        for node in to_replace.iter() {
            Self::btree_replace(set, node, node.clone().kill(location));
        }
    }

    /// Tags all untagged places which have to_tag as a prefix in a set of edges
    /// Bad performance (probably)
    fn tag_in_edge_set(
        set: &mut BTreeSet<CDGEdge<'tcx>>,
        location: PointIndex,
        to_tag: mir::Place<'tcx>,
    ) {
        let new_set: BTreeSet<CDGEdge<'tcx>> = BTreeSet::default();
        for mut edge in set.clone().into_iter() {
            Self::tag_in_set(&mut edge.lhs, location, to_tag);
            Self::tag_in_set(&mut edge.rhs, location, to_tag);
        }
        *set = new_set;
    }

    /// Tags all untagged places which have to_tag as a prefix
    pub fn tag(&mut self, location: PointIndex, to_tag: mir::Place<'tcx>) {
        Self::tag_in_set(&mut self.roots, location, to_tag);
        Self::tag_in_set(&mut self.leaves, location, to_tag);
        Self::tag_in_edge_set(&mut self.edges, location, to_tag);
    }
}

// A coupling graph
#[derive(Clone, Default, PartialEq, Eq)]
pub struct CDG<'tcx> {
    pub origins: BTreeMap<Region, CDGOrigin<'tcx>>,
    pub subset_invariant: bool,
    pub origin_contains_loan_at_invariant: bool,
}

impl<'tcx> CDG<'tcx> {
    /// Apply a function to all origins in the graph
    pub fn mutate_origins_uniform<'a, 's: 'a>(
        &'s mut self,
        f: fn(Region, &'a mut CDGOrigin<'tcx>),
    ) {
        for (origin, cdg_origin) in self.origins.iter_mut() {
            f(*origin, cdg_origin);
        }
    }
}

#[derive(Clone)]
pub struct CouplingState<'facts, 'mir: 'facts, 'tcx: 'mir> {
    pub coupling_graph: CDG<'tcx>,
    pub to_kill: ToKill<'tcx>,
    // Also include: invariant checks, loan kill marks
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
    fact_table: &'facts FactTable<'tcx>,
}

#[derive(PartialEq, Eq, Clone, Debug, Default)]
pub struct ToKill<'tcx> {
    pub loans: BTreeSet<(Loan, PointIndex)>,
    pub places: BTreeSet<(mir::Place<'tcx>, PointIndex)>,
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> CouplingState<'facts, 'mir, 'tcx> {
    pub(crate) fn new_empty(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        fact_table: &'facts FactTable<'tcx>,
    ) -> Self {
        Self {
            coupling_graph: Default::default(),
            to_kill: Default::default(),
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
        self.apply_loan_moves(location)?;
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
        let origin_set = match self.fact_table.origin_contains_loan_at.get(location) {
            Some(ocla_set) => ocla_set.keys().cloned().collect::<BTreeSet<_>>(),
            None => BTreeSet::default(),
        };

        // (expiries) Remove all origins which are not in that set
        //  todo: calculate and log the FPCS effects at this point
        self.coupling_graph
            .origins
            .retain(|k, _| origin_set.contains(k));

        // (issues) Include empty origins for each new origin
        for origin in origin_set.iter() {
            self.coupling_graph.origins.entry(*origin).or_default();
        }

        // Sanity check
        assert_eq!(
            self.coupling_graph
                .origins
                .keys()
                .cloned()
                .collect::<BTreeSet<_>>(),
            origin_set
        );

        Ok(())
    }

    /// Issue all new borrow temporaries into their appropriate loans, if they exist.
    fn apply_loan_issues(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        if let Some((issuing_origin, borrowed_from_place)) =
            self.fact_table.loan_issues.get(location)
        {
            // Issuing origin should be empty
            assert!(self
                .coupling_graph
                .origins
                .get(issuing_origin)
                .unwrap()
                .is_empty());

            // Issuing origin LHS should be a borrow
            let issued_loan = match self.fact_table.origins.map.get(issuing_origin).unwrap() {
                OriginLHS::Place(_) => panic!(),
                OriginLHS::Loan(issued_loan) => issued_loan,
            };

            // Set the origin to be a loan from the LHS to RHS
            let issuing_edge = CDGEdge::loan_edge(*issued_loan, *borrowed_from_place);
            self.coupling_graph
                .origins
                .get_mut(issuing_origin)
                .unwrap()
                .insert_edge(issuing_edge);

            // Check for reborrows: (fixme: unimplemented)
            //      If there is a reborrow, it should be the case that the borrowed_from_place
            //      is equal to the LHS of the borrowed_from_origin (ie. packing) due to the issued packing constraints.
            //      Add an edge between the two.
        }
        Ok(())
    }

    /// For every loan move:
    ///     - Kill the RHS of the move, unless it's a borrow
    ///     - Unpack the RHS to meet the packing requirement
    fn apply_loan_moves(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        for (from, to) in self.fact_table.get_moves_at(location) {
            // Kill the RHS place
            // fixme: implement

            // Add an edge from
            // fixme: implement
        }
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
        let mut s = serializer.serialize_struct("[coupling state]", 2)?;
        s.serialize_field("[kills]", &self.to_kill)?;
        s.serialize_field("[cdg]", &self.coupling_graph)?;
        s.end()
    }
}

impl<'tcx> Serialize for ToKill<'tcx> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut s = serializer.serialize_struct("[kills]", 2)?;
        s.serialize_field("loans", &format!("{:?}", self.loans))?;
        s.serialize_field("places", &format!("{:?}", self.places))?;
        s.end()
    }
}

impl<'tcx> Serialize for CDG<'tcx> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(None)?;
        map.serialize_entry("subset invariant?", &self.subset_invariant)?;
        map.serialize_entry(
            "origins invariant?",
            &self.origin_contains_loan_at_invariant,
        )?;
        for (o, cdg) in self.origins.iter() {
            map.serialize_entry(&format!("{:?}", o), &format!("{:?}", cdg))?;
        }
        map.end()
    }
}

impl fmt::Debug for CouplingState<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[coupling state] {}",
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
