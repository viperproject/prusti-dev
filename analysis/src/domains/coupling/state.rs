// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use log::info;

use crate::{
    abstract_interpretation::{AbstractState, AnalysisResult, OriginLHS},
    mir_utils::{self, is_prefix, Place, PlaceImpl},
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

impl<'tcx> Into<CDGNode<'tcx>> for OriginLHS<'tcx> {
    // Turn an OriginLHS into a CDGNode by creating a new untagged node
    fn into(self) -> CDGNode<'tcx> {
        match self {
            OriginLHS::Place(p) => CDGNode::Place(Tagged::untagged(p)),
            OriginLHS::Loan(l) => CDGNode::Borrow(Tagged::untagged(l)),
        }
    }
}

/// Nodes for the coupling digraph
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CDGNode<'tcx> {
    Place(Tagged<Place<'tcx>, PointIndex>),
    Borrow(Tagged<Loan, PointIndex>),
}

impl<'tcx> fmt::Debug for CDGNode<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CDGNode::Place(tp) => {
                if let Some(tag) = tp.tag {
                    write!(f, "{:?}@{:?}", tp.data, tag.index())
                } else {
                    write!(f, "{:?}", tp.data)
                }
            }
            CDGNode::Borrow(tb) => {
                if let Some(tag) = tb.tag {
                    write!(f, "{:?}@{:?}", tb.data, tag.index())
                } else {
                    write!(f, "{:?}", tb.data)
                }
            }
        }
    }
}

impl<'tcx> CDGNode<'tcx> {
    // Kills a node, if it isn't already unkilled
    pub fn kill(mut self, l: &PointIndex) -> Self {
        match &mut self {
            CDGNode::Place(p) => p.tag(*l),
            CDGNode::Borrow(b) => b.tag(*l),
        }
        self
    }

    // Should a given node be killed if we are trying to kill another node?
    fn should_tag(&self, to_kill: &CDGNode<'tcx>) -> bool {
        match (self, to_kill) {
            (CDGNode::Place(p_self), CDGNode::Place(p_kill)) => {
                p_self.tag.is_none() && p_kill.tag.is_none() && is_prefix(p_self.data, p_kill.data)
            }
            (l0 @ CDGNode::Borrow(_), l1 @ CDGNode::Borrow(_)) => l0 == l1,
            _ => false,
        }
    }
}

/// Corresponds to the annotations we store in the CDG
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum CDGEdgeKind {
    Borrow,
    Reborrow,
    Move,
}

// Coupling graph hyper-edges
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug)]
pub struct CDGEdge<'tcx> {
    pub lhs: BTreeSet<CDGNode<'tcx>>,
    pub rhs: BTreeSet<CDGNode<'tcx>>,
    pub edge: CDGEdgeKind,
}

impl<'tcx> CDGEdge<'tcx> {
    pub fn loan_edge(loan: Loan, place: Place<'tcx>) -> Self {
        Self {
            lhs: BTreeSet::from_iter([CDGNode::Borrow(Tagged::untagged(loan))].into_iter()),
            rhs: BTreeSet::from_iter([CDGNode::Place(Tagged::untagged(place.into()))].into_iter()),
            edge: CDGEdgeKind::Borrow,
        }
    }

    pub fn move_edge(
        assignee_cannonical_lhs: BTreeSet<CDGNode<'tcx>>,
        assign_from_real_lhs: BTreeSet<CDGNode<'tcx>>,
    ) -> Self {
        Self {
            lhs: assignee_cannonical_lhs,
            rhs: assign_from_real_lhs,
            edge: CDGEdgeKind::Move,
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
        self.edges.insert(edge);
        self.recompute_signature();
    }

    fn recompute_signature(&mut self) {
        // fixme: Collections interface doesn't like chaining unions
        //  maybe  a map/fold does better here?
        let mut all_lhs: BTreeSet<CDGNode<'tcx>> = BTreeSet::default();
        let mut all_rhs: BTreeSet<CDGNode<'tcx>> = BTreeSet::default();
        for edge in self.edges.iter() {
            all_lhs = all_lhs.union(&edge.lhs).cloned().collect();
            all_rhs = all_rhs.union(&edge.rhs).cloned().collect();
        }
        self.leaves = all_lhs.difference(&all_rhs).cloned().collect();
        self.roots = all_rhs.difference(&all_lhs).cloned().collect();
    }

    /// Adds an edge if it does not already exist
    ///  Returns true if a new edge was added
    pub fn enforce_edge(&mut self, edge: &CDGEdge<'tcx>) -> bool {
        if !self.edges.contains(edge) {
            self.insert_edge((*edge).clone());
            return true;
        }
        return false;
    }

    /// Replace a node in a BTreeSet
    fn btree_replace<T: Ord>(btree: &mut BTreeSet<T>, from: &T, to: T) {
        if btree.remove(from) {
            btree.insert(to);
        }
    }

    /// Tags all untagged places which have to_tag as a prefix in a set of nodes
    ///
    fn tag_in_set(
        set: &mut BTreeSet<CDGNode<'tcx>>,
        location: &PointIndex,
        to_tag: &CDGNode<'tcx>,
    ) {
        let mut to_replace: Vec<CDGNode<'tcx>> = vec![];
        for node in set.iter() {
            if node.should_tag(to_tag) {
                to_replace.push((*node).clone())
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
        location: &PointIndex,
        to_tag: &CDGNode<'tcx>,
    ) {
        let owned_set = std::mem::take(set);
        for mut edge in owned_set.into_iter() {
            Self::tag_in_set(&mut edge.lhs, location, to_tag);
            Self::tag_in_set(&mut edge.rhs, location, to_tag);
            set.insert(edge);
        }
    }

    /// Tags all untagged places which have to_tag as a prefix
    pub fn tag(&mut self, location: &PointIndex, to_tag: &CDGNode<'tcx>) {
        Self::tag_in_set(&mut self.roots, location, to_tag);
        Self::tag_in_set(&mut self.leaves, location, to_tag);
        Self::tag_in_edge_set(&mut self.edges, location, to_tag);
    }
}

// A coupling graph
#[derive(Clone, Default, PartialEq, Eq, Debug)]
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

    /// Ensure all edges from origin "sub" are contained in "sup"
    /// Return true if there is a change
    pub fn enforce_subset(&mut self, sub: &Region, sup: &Region) -> bool {
        let mut result = false;
        let sub_edges: Vec<_> = self
            .origins
            .get(sub)
            .unwrap()
            .edges
            .iter()
            .cloned()
            .collect();
        for sub_edge in sub_edges.iter() {
            let changed = self.origins.get_mut(sup).unwrap().enforce_edge(&sub_edge);
            result = result || changed;
        }
        return result;
    }

    // Kill an OriginLHS in all origins
    fn kill_node(&mut self, location: &PointIndex, node: &CDGNode<'tcx>) -> AnalysisResult<()> {
        // let graph = std::mem::take(&mut self.origins);
        // for (origin, mut cdg_origin) in graph.into_iter() {
        //     cdg_origin.tag(location, node);
        //     self.origins.insert(origin, cdg_origin);
        // }
        // Ok(())
        for cdg_origin in self.origins.values_mut() {
            cdg_origin.tag(location, node);
        }
        Ok(())
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
        self.enforce_subset_invariant(location)?;
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

    fn apply_loan_moves(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        for (from, to) in self.fact_table.get_move_origins_at(location) {
            // Kill every place in the to-origins's current LHS
            // let to_origin_current_lhs = self.coupling_graph.origins.get(&to).unwrap().roots.clone();
            // for origin_lhs in to_origin_current_lhs.iter() {
            //     if let CDGNode::Place(p) = origin_lhs {
            //         self.coupling_graph
            //             .origins
            //             .get_mut(&to)
            //             .unwrap()
            //             .tag(location, origin_lhs);
            //     }
            // }

            // Kill every place that is a prefix of this set:
            let mut from_origin_current_lhs = self
                .coupling_graph
                .origins
                .get(&from)
                .unwrap()
                .leaves
                .clone();

            for origin_lhs in from_origin_current_lhs.iter() {
                if let node @ CDGNode::Place(_) = origin_lhs {
                    // Kill origin_lhs in all places in the graph
                    self.coupling_graph.kill_node(location, node)?;
                }
            }
            // Get the to-origin's LHS (this is already repacked to be the LHS of the assignment)
            let to_origin_assigning_lhs: BTreeSet<CDGNode<'tcx>> =
                BTreeSet::from([(*self.fact_table.origins.map.get(&to).unwrap())
                    .clone()
                    .into()]);

            // Get the from-origin's new LHS (these should be killed, now)
            from_origin_current_lhs = self
                .coupling_graph
                .origins
                .get(&from)
                .unwrap()
                .leaves
                .clone();

            // Add an edge from the to-origins's assigning LHS (a set of untagged places) to the LHS of the from-origin (a set of tagged places)
            self.coupling_graph
                .origins
                .get_mut(&to)
                .unwrap()
                .insert_edge(CDGEdge::move_edge(
                    to_origin_assigning_lhs,
                    from_origin_current_lhs,
                ));
        }
        Ok(())
    }

    /// For every loan_killed_at at this location, mark the killed place
    fn mark_kills(&mut self) -> AnalysisResult<()> {
        // fixme: implement
        Ok(())
    }

    /// Check that every subset at a location is true.
    ///     That is, for every subset #a<:#b copy the edges from #a into #b
    ///     Iterate until we reach a fixed point (or come up with a smarter solution)
    fn enforce_subset_invariant(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        if let Some(subsets) = self.fact_table.subsets_at.get(location) {
            let mut changed = true;
            while changed {
                changed = false;
                for (sub, sup_set) in subsets.iter() {
                    for sup in sup_set.iter() {
                        let iter_changed = self.coupling_graph.enforce_subset(sub, sup);
                        changed = changed || iter_changed;
                    }
                }
            }
        }
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
