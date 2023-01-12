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
    borrowck::{consumers::RustcFacts, BodyWithBorrowckFacts},
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::{mir, mir::Location},
    polonius_engine::FactTypes,
};
use serde::{ser::SerializeStruct, Serialize, Serializer};
use std::{collections::BTreeSet, fmt, mem, rc::Rc};

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
#[derive(Clone, PartialEq, Eq)]
pub struct CDGOrigin<'tcx> {
    edges: BTreeSet<CDGEdge<'tcx>>,
    leaves: BTreeSet<Rc<CDGNode<'tcx>>>,
    roots: BTreeSet<Rc<CDGNode<'tcx>>>,
}

// A coupling graph
#[derive(Clone, Default, PartialEq, Eq)]
pub struct CDG<'tcx> {
    pub origins: FxHashMap<Region, CDGOrigin<'tcx>>,
}

#[derive(Clone)]
pub struct CouplingState<'mir, 'tcx: 'mir> {
    coupling_graph: CDG<'tcx>,
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
}

impl<'mir, 'tcx: 'mir> CouplingState<'mir, 'tcx> {
    pub fn check_invariant(&self, location: impl fmt::Debug) -> bool {
        todo!("check the Polonius invariants and determine if they hold")
    }

    pub(crate) fn new_empty(mir: &'mir BodyWithBorrowckFacts<'tcx>) -> Self {
        Self {
            coupling_graph: Default::default(),
            mir,
        }
    }

    pub(crate) fn apply_terminator_effect(
        &self,
        location: Location,
    ) -> AnalysisResult<Vec<(mir::BasicBlock, Self)>> {
        let mut res_vec = Vec::new();
        let terminator = self.mir.body[location.block].terminator();
        for bb in terminator.successors() {
            res_vec.push((bb, self.clone()));
        }
        Ok(res_vec)
    }
}

impl<'mir, 'tcx: 'mir> Serialize for CouplingState<'mir, 'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut s = serializer.serialize_struct("CouplingState", 1)?;
        s.serialize_field("fixme", "fixme")?;
        s.end()
    }
}

impl fmt::Debug for CouplingState<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CDG (fixme) {}",
            serde_json::to_string_pretty(&self).unwrap()
        )
    }
}

impl<'mir, 'tcx: 'mir> PartialEq for CouplingState<'mir, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.coupling_graph == other.coupling_graph
    }
}

impl<'mir, 'tcx: 'mir> Eq for CouplingState<'mir, 'tcx> {}

impl<'mir, 'tcx: 'mir> AbstractState for CouplingState<'mir, 'tcx> {
    fn is_bottom(&self) -> bool {
        // todo: remove stub
        false
    }

    fn join(&mut self, other: &Self) {
        // todo: remove stub
    }

    fn widen(&mut self, previous: &Self) {
        // todo: remove stub
    }
}
