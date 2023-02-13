// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use log::info;

use crate::{
    abstract_interpretation::{AbstractState, AnalysisResult},
    mir_utils::{self, expand, expand_struct_place, is_prefix, Place},
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
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use super::{
    btree_replace,
    facts::{FactTable, OriginLHS},
};

// These types are stolen from Prusti interface
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

/// A CDGNode represents a permission (a node in the coupling graph)
/// A CDGNode is one of
///     - A Place: a mir_utils::Place, tagged by a point
///     - A Borrow: a Loan, tagged by a point
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CDGNode<'tcx> {
    Place(Tagged<Place<'tcx>, PointIndex>),
    Borrow(Tagged<Loan, PointIndex>),
}

impl<'tcx> CDGNode<'tcx> {
    /// Tags a node at a point, if it isn't already untagged
    pub fn kill(mut self, l: &PointIndex) -> Self {
        match &mut self {
            CDGNode::Place(p) => p.tag(*l),
            CDGNode::Borrow(b) => b.tag(*l),
        }
        self
    }

    /// Determine if a kill should tag the current place:
    ///     - A borrow should be tagged only if it is untagged, and equal to to_kill
    ///     - A place should be tagged only if it is untagged, and to_kill is its prefix
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

impl<'tcx> Into<CDGNode<'tcx>> for OriginLHS<'tcx> {
    /// Turn an OriginLHS into a CDGNode by creating a new untagged node
    fn into(self) -> CDGNode<'tcx> {
        match self {
            OriginLHS::Place(p) => CDGNode::Place(Tagged::untagged(p)),
            OriginLHS::Loan(l) => CDGNode::Borrow(Tagged::untagged(l)),
        }
    }
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

/// Corresponds to the annotations we store in the CDG
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum CDGEdgeKind {
    Borrow,
    Reborrow,
    Move,
    Unpack,
    Coupled(BTreeSet<Loan>),
}

/// Edges in the coupling graph
/// Each edge consists of a signature (lhs --* rhs) and a kind
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug)]
pub struct CDGEdge<'tcx> {
    pub lhs: BTreeSet<CDGNode<'tcx>>,
    pub rhs: BTreeSet<CDGNode<'tcx>>,
    pub edge: CDGEdgeKind,
}

impl<'tcx> CDGEdge<'tcx> {
    /// Construct an edge corresponding to a loan
    pub fn loan_edge(loan: Loan, place: Place<'tcx>) -> Self {
        Self {
            lhs: [CDGNode::Borrow(Tagged::untagged(loan))].into(),
            rhs: [CDGNode::Place(Tagged::untagged(place.into()))].into(),
            edge: CDGEdgeKind::Borrow,
        }
    }

    /// Construct an edge corresponding to a move
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

    /// Construct an edge corresponding to an unpack operation
    pub fn unpack_edge(unpacked: BTreeSet<CDGNode<'tcx>>, packed: BTreeSet<CDGNode<'tcx>>) -> Self {
        Self {
            lhs: unpacked,
            rhs: packed,
            edge: CDGEdgeKind::Unpack,
        }
    }
}

/// The fragment of a coupling graph associated with an origin
/// Each coupling graph has a signature (leaves --* roots) computed by the annotations in its edges
#[derive(Clone, Default, PartialEq, Eq)]
pub struct CDGOrigin<'tcx> {
    pub(crate) edges: BTreeSet<CDGEdge<'tcx>>,
    leaves: BTreeSet<CDGNode<'tcx>>,
    roots: BTreeSet<CDGNode<'tcx>>,
}

impl<'tcx> CDGOrigin<'tcx> {
    /// A CDG fragment is empty when it contains no edges (so has a trivial signature)
    pub fn is_empty(&self) -> bool {
        self.edges.is_empty() && self.leaves.is_empty() && self.leaves.is_empty()
    }

    /// Insert an edge into a CDG fragment and recompute its signature
    /// fixme: this doesn't prevent cyclic graphs, which would have trivial signature.
    pub fn insert_edge(&mut self, edge: CDGEdge<'tcx>) {
        self.edges.insert(edge);
        self.recompute_signature();
    }

    pub fn new_coupling(
        lhs: BTreeSet<CDGNode<'tcx>>,
        rhs: BTreeSet<CDGNode<'tcx>>,
        loans: BTreeSet<Loan>,
    ) -> Self {
        Self {
            edges: [CDGEdge {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
                edge: CDGEdgeKind::Coupled(loans),
            }]
            .into(),
            leaves: lhs,
            roots: rhs,
        }
    }

    /// Determine the signautre of a CDG fragment from its edges
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

    /// Ensures that the CDG fragment contains an edge
    ///     returns True if the edge was not already in the graph
    pub fn enforce_edge(&mut self, edge: &CDGEdge<'tcx>) -> bool {
        if !self.edges.contains(edge) {
            self.insert_edge((*edge).clone());
            return true;
        }
        return false;
    }

    /// If Other is a subset of self, remove the edges from self.
    /// Return True if self was changed
    pub fn remove_if_subset(&mut self, other: &Self) -> bool {
        if other.edges.is_subset(&self.edges) {
            for e in other.edges.iter() {
                self.edges.remove(e);
            }
            self.recompute_signature();
            return true;
        }
        return false;
    }

    /// Tags all untagged places which have to_tag as a prefix in a set of nodes
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
            btree_replace(set, node, node.clone().kill(location));
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

    pub(crate) fn roots(&self) -> &BTreeSet<CDGNode<'tcx>> {
        &self.roots
    }

    pub(crate) fn leaves(&self) -> &BTreeSet<CDGNode<'tcx>> {
        &self.leaves
    }
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

pub type OriginMap<'tcx> = BTreeMap<Region, CDGOrigin<'tcx>>;

/// CouplingOrigins represents many copies of graphs to be analyzed at each program point
/// Each graph is represented as a map from origins to fragments of the graph
#[derive(Default, Eq, Clone)]
pub struct CouplingOrigins<'tcx> {
    pub origins: Vec<OriginMap<'tcx>>,
}

impl<'tcx> CouplingOrigins<'tcx> {
    /// New CouplingOrigins which contains one empty graph
    pub fn new_empty() -> Self {
        Self {
            origins: vec![Default::default()],
        }
    }

    /// Ensure that all origins from origin "sub" are contained in "sup"
    /// Return true if there is a change to the graph
    pub fn enforce_subset(&mut self, sub: &Region, sup: &Region) -> bool {
        let mut result = false;
        for origin_map in self.origins.iter_mut() {
            let sub_edges: Vec<_> = origin_map.get(sub).unwrap().edges.iter().cloned().collect();
            for sub_edge in sub_edges.iter() {
                let changed = origin_map.get_mut(sup).unwrap().enforce_edge(&sub_edge);
                result = result || changed;
            }
        }
        return result;
    }

    /// Kill a node in all graphs at a location
    fn kill_node(&mut self, location: &PointIndex, node: &CDGNode<'tcx>) -> AnalysisResult<()> {
        for cdg_origin_map in self.origins.iter_mut() {
            for cdg_origin in cdg_origin_map.values_mut() {
                cdg_origin.tag(location, node);
            }
        }
        Ok(())
    }

    /// Check that two CouplingOrigins have the same LHS's for each origin they both have
    fn cohere_lhs(&mut self, other: &CouplingOrigins<'tcx>) {
        // Join the two by appending the origins together

        // Now we must ensure the two sets of origin mappings cohere, that is they
        //  have the same LHS for each non-empty origin.
        // fixme: right now we just panic if they are incoherent, but in reality we should
        // probably fix them by repacking.

        // naive hack solution: iterate over all tuples
        for origin_map in self.origins.iter() {
            for (origin, cdgo) in origin_map.iter() {
                for other_origin_map in self.origins.iter() {
                    if let Some(other_cdgo) = other_origin_map.get(origin) {
                        assert_eq!(cdgo.leaves, other_cdgo.leaves);
                    }
                }
            }
        }
    }

    /// Get all leaves of an origin (in all branches).
    /// The leaf sets for an origin should be identical, including repackings, in all graphs.
    fn get_leaves(&self, origin: &Region) -> BTreeSet<CDGNode<'tcx>> {
        let mut lhs: Option<&BTreeSet<CDGNode<'tcx>>> = None;
        for leaf_set in self
            .origins
            .iter()
            .map(|origin_map| &origin_map.get(origin).unwrap().leaves)
        {
            if lhs.is_none() {
                lhs = Some(leaf_set)
            } else {
                assert_eq!(lhs, Some(leaf_set));
            }
        }
        return lhs.and_then(|s| Some((*s).clone())).unwrap();
    }

    /// Kill all leaves that are the LHS of a region
    pub fn kill_leaves(&mut self, origin: &Region, location: &PointIndex) -> AnalysisResult<()> {
        for leaf in self.get_leaves(origin) {
            self.kill_node(location, &leaf)?;
        }
        Ok(())
    }
}

impl<'tcx> PartialEq for CouplingOrigins<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.origins
            .iter()
            .all(|origins_map| other.origins.contains(origins_map))
            && other
                .origins
                .iter()
                .all(|origins_map| self.origins.contains(origins_map))
    }
}

impl<'tcx> fmt::Debug for CouplingOrigins<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for origins_map in self.origins.iter() {
            write!(f, "[[{:?}]]", origins_map)?;
        }
        Ok(())
    }
}

// A coupling graph
//  A coupling grpah a CDGOrigins (the map from origins to fragments of the graph)
//  and some metadata
#[derive(Clone, Default, PartialEq, Eq)]
pub struct CDG<'tcx> {
    pub origins: CouplingOrigins<'tcx>,
    pub origin_contains_loan_at_invariant: bool,
}

impl<'tcx> CDG<'tcx> {
    pub fn new_empty() -> Self {
        Self {
            origins: CouplingOrigins::new_empty(),
            origin_contains_loan_at_invariant: false,
        }
    }

    // Ensure all edges from origin "sub" are contained in "sup"
    // Return true if there is a change
    // pub fn enforce_subset(&mut self, sub: &Region, sup: &Region) -> bool {
    //     self.origins.enforce_subset(sub, sup)
    // }

    // Kill an OriginLHS in all origins
    // fn kill_node(&mut self, location: &PointIndex, node: &CDGNode<'tcx>) -> AnalysisResult<()> {
    //     self.origins.kill_node(location, node)
    // }
}

impl<'tcx> fmt::Debug for CDG<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "CDG(ocla_invariant? {:?})",
            self.origin_contains_loan_at_invariant
        )?;

        let mut counter: usize = 0;
        for origin in self.origins.origins.iter() {
            if origin.is_empty() {
                writeln!(f, "\t<group {:?}> Empty", counter)?;
            } else {
                writeln!(f, "\t<group {:?}>", counter)?;
                for (o, s) in origin.iter() {
                    writeln!(f, "\t\t{:?}: {:?}", o, s)?;
                }
            }
            counter += 1;
        }
        Ok(())
    }
}

/// ToKill is a helper data structure for tracking places to tag.
#[derive(PartialEq, Eq, Clone, Debug, Default)]
pub struct ToKill<'tcx> {
    pub loans: BTreeSet<(Loan, PointIndex)>,
    pub places: BTreeSet<(Place<'tcx>, PointIndex)>,
}
impl<'tcx> ToKill<'tcx> {
    fn is_empty(&self) -> bool {
        self.loans.is_empty() && self.places.is_empty()
    }

    pub fn mark_loan(&mut self, loan: Loan, point: PointIndex) {
        assert!(self.loans.insert((loan, point)));
    }

    pub fn mark_place(&mut self, place: Place<'tcx>, point: PointIndex) {
        assert!(self.places.insert((place, point)));
    }

    pub fn apply_all(&mut self, graph: &mut CDG<'tcx>) -> AnalysisResult<()> {
        // fixme: this should not be possible, but nothing in the data structure is preventing
        // a loan to be killed by multiple points. revisit when considering function calls.
        for (loan, point) in self.loans.iter() {
            graph
                .origins
                .kill_node(point, &CDGNode::Borrow(Tagged::untagged(*loan)))?;
        }
        for (place, point) in self.places.iter() {
            graph
                .origins
                .kill_node(point, &CDGNode::Place(Tagged::untagged(*place)))?;
        }
        self.loans = Default::default();
        self.places = Default::default();
        Ok(())
    }
}

/// CouplingState consists of
///     - A CouplingGraph, representing the current
///     - Some nodes to kill between this statement and the next
///     - References to the context mir and fact_table
#[derive(Clone)]
pub struct CouplingState<'facts, 'mir: 'facts, 'tcx: 'mir> {
    pub coupling_graph: CDG<'tcx>,
    pub to_kill: ToKill<'tcx>,
    // Also include: invariant checks, loan kill marks
    pub(crate) mir: &'mir BodyWithBorrowckFacts<'tcx>,
    pub(crate) fact_table: &'facts FactTable<'tcx>,
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> CouplingState<'facts, 'mir, 'tcx> {
    pub(crate) fn new_empty(
        mir: &'mir BodyWithBorrowckFacts<'tcx>,
        fact_table: &'facts FactTable<'tcx>,
    ) -> Self {
        Self {
            coupling_graph: CDG::new_empty(),
            to_kill: Default::default(),
            fact_table,
            mir,
        }
    }

    pub(crate) fn new_bottom(
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
        println!(
            "[debug@{:?}] {:?}",
            self.mir.location_table.start_index(location),
            self.coupling_graph
        );
        // println!("[inference]   enter {:?}", RichLocation::Mid(location));
        self.apply_polonius_inference(&self.mir.location_table.mid_index(location))?;
        println!(
            "[debug@{:?}] {:?}",
            self.mir.location_table.mid_index(location),
            self.coupling_graph
        );
        Ok(())
    }

    /// The main interpretation of Polonius facts
    fn apply_polonius_inference(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        self.apply_marked_kills()?;
        self.apply_origins(location)?;
        self.apply_packing_requirements(location, &self.mir.body, self.fact_table.tcx)?;
        self.apply_loan_issues(location)?;
        self.apply_loan_moves(location)?;
        self.enforce_subset_invariant(location)?;
        self.check_origin_contains_loan_at_invariant()?;
        self.mark_kills(location)?;
        Ok(())
    }

    /// Repack the LHS of an origin to contain some place, and add edges to
    /// RHS's as appropriate to ensure connectivity.
    fn apply_packing_requirements(
        &mut self,
        location: &PointIndex,
        mir: &mir::Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> AnalysisResult<()> {
        for origin_map in self.coupling_graph.origins.origins.iter_mut() {
            // ok if is some and can be repacked, or current lhs is none and packing requiremt is cannonical origin
            if let Some(reqs) = self.fact_table.origin_packing_at.get(location) {
                for (origin, place) in reqs.iter() {
                    let current_leaves = origin_map
                        .get(origin)
                        .and_then(|o| Some(o.leaves.clone()))
                        .unwrap();
                    if current_leaves.is_empty() {
                        println!("[debug]   getting cannonical roots for {:?}", origin);
                        let cannonical_roots = self.fact_table.origins.map.get(origin).unwrap();
                        assert_eq!(place, cannonical_roots);
                    } else {
                        // Try to repack the set of elements current_leaves to include place
                        // fixme: this is not a real repacker! this is a small hack
                        // which only creates unpack edges, or panics.
                        // 0. expect that place is actually a place, and is untagged
                        let target_place = match place {
                            OriginLHS::Place(tp) => tp,
                            OriginLHS::Loan(_) => {
                                panic!("internal error, can't meet a pack requirement for a loan")
                            }
                        };

                        // 1. exclude borrows and tagged places
                        let mut leaf_set: BTreeSet<mir_utils::Place<'tcx>> = current_leaves
                            .iter()
                            .filter_map(|node| {
                                if let CDGNode::Place(tp) = node {
                                    if let None = tp.tag {
                                        Some(&tp.data)
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            })
                            .cloned()
                            .collect();

                        // 2. Find the closest leaf (there should be exactly one leaf which is a prefix of place)
                        let mut closest_leaf = match leaf_set
                            .iter()
                            .filter(|p| is_prefix(*target_place, **p))
                            .cloned()
                            .collect::<Vec<_>>()[..]
                        {
                            [closest_leaf] => closest_leaf,
                            _ => {
                                // fixme: try to pack up by removing unpack edges in this case
                                unimplemented!(
                                    "internal error, no closest leaf to {:?} for unpacker in {:?}",
                                    target_place,
                                    leaf_set
                                )
                            }
                        };

                        while !leaf_set.contains(target_place) {
                            // 3. Unpack it
                            let closest_expansion = closest_leaf.expand(target_place, mir, tcx);

                            // 4. Replace the closest leaf with the unpacked version in the leaf_set
                            leaf_set.remove(&closest_leaf);
                            for new_leaf in closest_expansion.iter().cloned() {
                                leaf_set.insert(new_leaf.into());
                            }

                            // 5. Push a new unpack edge to origin
                            origin_map.entry(*origin).and_modify(|e| {
                                e.insert_edge(CDGEdge::unpack_edge(
                                    closest_expansion
                                        .into_iter()
                                        .map(|p| CDGNode::Place(Tagged::untagged(p.into())))
                                        .collect::<_>(),
                                    BTreeSet::from([CDGNode::Place(Tagged::untagged(
                                        (*closest_leaf).into(),
                                    ))]),
                                ))
                            });

                            // 6. Check that place is still a subset of some leaf (ie closest_leaf still exists)
                            closest_leaf = match leaf_set
                                .iter()
                                .filter(|p| is_prefix(*target_place, **p))
                                .cloned()
                                .collect::<Vec<_>>()[..]
                            {
                                [closest_leaf] => closest_leaf,
                                _ => panic!("internal error, no closest leaf for unpacker"),
                            };
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// For every loan which is marked as killed, kill it and remove the kill mark.
    fn apply_marked_kills(&mut self) -> AnalysisResult<()> {
        // fixme: implement
        self.to_kill.apply_all(&mut self.coupling_graph)?;
        Ok(())
    }

    /// Expire non-live origins, and add new live origins
    fn apply_origins(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        // Get the set of origins at a point from the origin_contains_loan_at fact
        let origin_set = match self.fact_table.origin_contains_loan_at.get(location) {
            Some(ocla_set) => ocla_set.keys().cloned().collect::<BTreeSet<_>>(),
            None => BTreeSet::default(),
        };

        for origin_map in self.coupling_graph.origins.origins.iter_mut() {
            // (expiries) Remove all origins which are not in that set
            //  todo: calculate and log the FPCS effects at this point
            origin_map.retain(|k, _| origin_set.contains(k));

            // (issues) Include empty origins for each new origin
            for origin in origin_set.iter() {
                origin_map.entry(*origin).or_default();
            }

            // Sanity check
            assert_eq!(
                origin_map.keys().cloned().collect::<BTreeSet<_>>(),
                origin_set
            );
        }
        Ok(())
    }

    /// Issue all new borrow temporaries into their appropriate loans, if they exist.
    fn apply_loan_issues(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        if let Some((issuing_origin, borrowed_from_place)) =
            self.fact_table.loan_issues.get(location)
        {
            for origin_map in self.coupling_graph.origins.origins.iter_mut() {
                // Issuing origin should be empty
                assert!(origin_map.get(issuing_origin).unwrap().is_empty());

                // Issuing origin LHS should be a borrow
                let issued_loan = match self.fact_table.origins.map.get(issuing_origin).unwrap() {
                    OriginLHS::Place(_) => panic!(),
                    OriginLHS::Loan(issued_loan) => issued_loan,
                };

                // Set the origin to be a loan from the LHS to RHS
                let issuing_edge = CDGEdge::loan_edge(*issued_loan, *borrowed_from_place);
                origin_map
                    .get_mut(issuing_origin)
                    .unwrap()
                    .insert_edge(issuing_edge);

                // Check for reborrows: (fixme: unimplemented)
                //      If there is a reborrow, it should be the case that the borrowed_from_place
                //      is equal to the LHS of the borrowed_from_origin (ie. packing) due to the issued packing constraints.
                //      Add an edge between the two.
            }
        }
        Ok(())
    }

    fn apply_loan_moves(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        for (from, to) in self.fact_table.get_move_origins_at(location) {
            // Kill every place in the to-origins's cannonical LHS (fixme: is this right? I want to kill the assigned-to place)
            if let OriginLHS::Place(mir_place) = self.fact_table.origins.map.get(&to).unwrap() {
                let node_to_kill = CDGNode::Place(Tagged::untagged(*mir_place));
                self.coupling_graph
                    .origins
                    .kill_node(location, &node_to_kill)?;
            };

            let mut nodes_to_kill: Vec<_> = Default::default();
            for origin_map in self.coupling_graph.origins.origins.iter_mut() {
                // Kill every place that is a prefix of this set:
                let from_origin_current_lhs = origin_map.get(&from).unwrap().leaves.clone();
                for origin_lhs in from_origin_current_lhs.iter() {
                    if let node @ CDGNode::Place(_) = origin_lhs {
                        // Kill origin_lhs in all places in the graph
                        nodes_to_kill.push(node.clone());
                    }
                }
            }

            for node in nodes_to_kill.into_iter() {
                self.coupling_graph.origins.kill_node(location, &node)?;
            }

            for origin_map in self.coupling_graph.origins.origins.iter_mut() {
                // Get the to-origin's LHS (this is already repacked to be the LHS of the assignment)
                let to_origin_assigning_lhs: BTreeSet<CDGNode<'tcx>> =
                    BTreeSet::from([(*self.fact_table.origins.map.get(&to).unwrap())
                        .clone()
                        .into()]);

                // Get the from-origin's new LHS (these should be killed, now)
                let from_origin_current_lhs = origin_map.get(&from).unwrap().leaves.clone();

                // Add an edge from the to-origins's assigning LHS (a set of untagged places) to the LHS of the from-origin (a set of tagged places)
                origin_map
                    .get_mut(&to)
                    .unwrap()
                    .insert_edge(CDGEdge::move_edge(
                        to_origin_assigning_lhs,
                        from_origin_current_lhs,
                    ));
            }
        }
        Ok(())
    }

    /// - For every loan_killed_at at this location, mark the killed place
    /// - if the MIR statement is a StorageDead and the location is a Start index, mark this place.
    fn mark_kills(&mut self, location: &PointIndex) -> AnalysisResult<()> {
        if let Some(kill_set) = self.fact_table.loan_killed_at.get(location) {
            for loan_to_kill in kill_set.iter() {
                self.to_kill.mark_loan(*loan_to_kill, *location);
            }
        }
        if let Some(place_to_kill) = FactTable::get_storage_dead_at(self.mir, *location) {
            self.to_kill.mark_place(place_to_kill, *location)
        }
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
                        let iter_changed = self.coupling_graph.origins.enforce_subset(sub, sup);
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
        let map = serializer.serialize_map(None)?;
        // fixme: stub
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
        self.to_kill.is_empty() && self.coupling_graph.origins.origins.is_empty()
    }

    // Invariant: bottom join X is X
    fn join(&mut self, other: &Self) {
        if !self.to_kill.is_empty() || !other.to_kill.is_empty() {
            unreachable!("(fixable) model assumes terminators do not kill places on exit");
        }
        println!("[join 1] {:?}", self.coupling_graph);
        println!("[join 2] {:?}", other.coupling_graph);

        self.coupling_graph
            .origins
            .cohere_lhs(&other.coupling_graph.origins);

        println!("[join coherent 1] {:?}", self.coupling_graph);
        println!("[join coherent 2] {:?}", other.coupling_graph);

        if self.coupling_graph != other.coupling_graph {
            if other.coupling_graph.origins.origins.is_empty() {
                // Nothing to do
            } else if self.coupling_graph.origins.origins.is_empty() {
                self.coupling_graph
                    .origins
                    .origins
                    .append(&mut other.coupling_graph.origins.origins.clone());
            } else {
                // fixme: this assumes no nested coupling (yet).

                // Look for (and couple) no-equal origins which have the same signature
                // good god... you need a origin lookup API at the coupling graph level
                let mut reborrows: BTreeSet<Region> = Default::default();
                for group in self.coupling_graph.origins.origins.iter() {
                    for (region, cdgo) in group.iter() {
                        for group1 in other.coupling_graph.origins.origins.iter() {
                            for (region1, cdgo1) in group1.iter() {
                                if (region == region1)
                                    && (cdgo.leaves == cdgo1.leaves)
                                    && (cdgo.roots == cdgo1.roots)
                                    && (cdgo != cdgo1)
                                {
                                    reborrows.insert(*region);
                                }
                            }
                        }
                    }
                }
                // fixme: ambiguous decision when groups differ
                for region in reborrows.into_iter() {
                    // fixme: this should do a root-first traversal for common structure
                    // fixme: it should also refer to the subsets at the point to decide which to simplify first. For example,
                    //      #1 : _3 -> _2 -> _1
                    //      #2 : _2 -> _1
                    //      #1 : _3 -> ... -> _3@p -> _2 -> _1
                    //      #2 : _2 -> _1
                    //  should not simplify #1 all together like
                    //      #1 : _3 --* _1
                    //  instead, since their downstream graphs are equal, we should get
                    //      #1 : _3 --* _2 -> _1
                    //      #2 : _2 -> _1

                    // Also, in the process of simplifying a edge of the form _3 -> ... -> _3@?
                    // we know that the last killed _3 is old(3). Can we unpick equality assertions from this?
                    if (self.coupling_graph.origins.origins.len() != 1)
                        || (other.coupling_graph.origins.origins.len() != 1)
                    {
                        unimplemented!("deferred joins of reborrows");
                    }

                    let other_cdgo = self.coupling_graph.origins.origins[0]
                        .get_mut(&region)
                        .unwrap()
                        .to_owned();
                    let self_cdgo = self.coupling_graph.origins.origins[0]
                        .get_mut(&region)
                        .unwrap();

                    if self_cdgo.remove_if_subset(&other_cdgo) {
                        // if self_cdgo can be decomposed as [current_self_cdgo] --> [other_cdgo]
                        // set the borrow to be the other_cdgo
                        // use difference to infer other aspects of the invariant

                        // get the loans contained in other_cdgo
                        let mut loans: BTreeSet<Loan> = Default::default();
                        for e in other_cdgo.edges.iter() {
                            for l in e.lhs.iter() {
                                if let CDGNode::Borrow(bw) = l {
                                    if bw.tag == None {
                                        loans.insert(bw.data);
                                    }
                                }
                            }
                        }

                        *self_cdgo = CDGOrigin::new_coupling(
                            other_cdgo.leaves.clone(),
                            other_cdgo.roots.clone(),
                            loans,
                        );
                    } else {
                        unimplemented!("reborrow that isn't structural subset");
                    }
                }

                // fixme: this assume the RHS are not in different packing states?

                // Couple origins which are possibly aliases
                //  Note that the origins are coherent so their LHS are equal
                //  - Partition origins by their RHS, in both sides.
                //  - If a RHS has only one origin, check that they are equal (or panic)
                //  - If a RHS has more than one origin, couple the LHS/RHS's of all the origins together.

                let mut couples: BTreeMap<BTreeSet<CDGNode<'tcx>>, BTreeSet<Region>> =
                    Default::default();

                for group in self.coupling_graph.origins.origins.iter() {
                    for (region, cdgo) in group.iter() {
                        (couples.entry(cdgo.roots.clone()).or_default()).insert(*region);
                    }
                }
                for group in other.coupling_graph.origins.origins.iter() {
                    for (region, cdgo) in group.iter() {
                        (couples.entry(cdgo.roots.clone()).or_default()).insert(*region);
                    }
                }

                println!("[coupling map I] {:?}", couples);

                let mut coupled_edges: BTreeMap<BTreeSet<Region>, BTreeSet<CDGNode>> =
                    Default::default();
                for (nodes, regions) in couples.into_iter() {
                    if let Some(node_set) = coupled_edges.get_mut(&regions) {
                        // Insert all nodes into node_set
                        for node in nodes.into_iter() {
                            node_set.insert(node);
                        }
                    } else {
                        coupled_edges.insert(regions, nodes);
                    }
                }

                println!("[coupling map II] {:?}", coupled_edges);

                let mut new_coupling_edges: BTreeMap<Region, CDGEdge<'tcx>> = Default::default();

                // Remove all singly coupled data and construct new coupling edges
                for (regions, rhs) in coupled_edges.into_iter() {
                    if regions.len() == 1 {
                        continue;
                    }

                    // Set of loans contained in any region of regions in any graph of self or other
                    let mut region_contains_loans: BTreeSet<Loan> = Default::default();

                    // fixme: do this in a less stupid way

                    for r in regions.iter() {
                        // For each region r in the set of coupled regions...
                        for group in self
                            .coupling_graph
                            .origins
                            .origins
                            .iter()
                            .chain(other.coupling_graph.origins.origins.iter())
                        {
                            // ... for each group in the two branches...
                            for e in group.get(r).unwrap().edges.iter() {
                                // ... for each loan in the LHS of an edge in the graph for r in the group...
                                for loan in e
                                    .lhs
                                    .iter()
                                    .filter_map(|n| match n {
                                        CDGNode::Place(_) => None,
                                        CDGNode::Borrow(l) => {
                                            if l.tag.is_none() {
                                                Some(l.data.clone())
                                            } else {
                                                None
                                            }
                                        }
                                    })
                                    .collect::<Vec<_>>()
                                {
                                    // ... add that loan to the set.
                                    region_contains_loans.insert(loan);
                                }
                            }
                        }
                    }

                    // // LHS of the edge is the union of all coupled edges
                    // let mut lhs: BTreeSet<CDGNode<'tcx>> = Default::default();
                    // for r in regions.iter() {
                    //     for n in self.coupling_graph.origins.origins[0]
                    //         .get(r)
                    //         .unwrap()
                    //         .leaves
                    //         .iter()
                    //     {
                    //         lhs.insert((*n).clone());
                    //     }
                    // }

                    // For each group in Self,
                    for r in regions.iter() {
                        for group in self.coupling_graph.origins.origins.iter_mut() {
                            let lhs: BTreeSet<CDGNode<'tcx>> = group.get(r).unwrap().leaves.clone();
                            group.insert(
                                *r,
                                CDGOrigin::new_coupling(
                                    lhs.clone(),
                                    rhs.clone(),
                                    region_contains_loans.clone(),
                                ),
                            );
                        }
                    }
                }

                println!("[coupling complete] {:?}", self.coupling_graph);
            }
        }
    }

    fn widen(&mut self, _: &Self) {
        unreachable!("widening is not possible in this model")
    }
}
