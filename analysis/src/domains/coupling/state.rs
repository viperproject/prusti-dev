// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// use log::info;
use crate::{abstract_interpretation::AbstractState, mir_utils::Place};
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
    lhs: BTreeSet<Rc<CDGNode<'tcx>>>,
    rhs: BTreeSet<Rc<CDGNode<'tcx>>>,
    edge: CDGEdgeKind,
}

/// The CDG graph fragments associated with an origin
/// Can be (roughly) interpreted as the Hoare triple
///     {leaves} edges {roots}
#[derive(Clone, PartialEq, Eq)]
pub struct CDGOrigin<'tcx> {
    pub edges: BTreeSet<CDGEdge<'tcx>>,
    pub leaves: BTreeSet<Rc<CDGNode<'tcx>>>,
    pub roots: BTreeSet<Rc<CDGNode<'tcx>>>,
}

// A coupling graph
#[derive(Clone, Default, PartialEq, Eq)]
pub struct CDG<'tcx> {
    pub origins: FxHashMap<Region, CDGOrigin<'tcx>>,
}

#[derive(Clone, Default, Eq, PartialEq)]
pub struct CouplingState<'tcx> {
    /// Placeholder
    coupling_graph: CDG<'tcx>,
}

impl<'tcx> CouplingState<'tcx> {
    pub fn check_invariant(&self, location: impl fmt::Debug) -> bool {
        todo!("check the invariants and determine if they hold")
    }
}

impl<'tcx> Serialize for CouplingState<'tcx> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut s = serializer.serialize_struct("CouplingState", 1)?;
        s.serialize_field("fixme", "fixme")?;
        s.end()
    }
}

impl fmt::Debug for CouplingState<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CDG (fixme) {}",
            serde_json::to_string_pretty(&self).unwrap()
        )
    }
}

impl<'mir> AbstractState for CouplingState<'mir> {
    fn is_bottom(&self) -> bool {
        todo!()
    }

    fn join(&mut self, other: &Self) {
        todo!()
    }

    fn widen(&mut self, previous: &Self) {
        todo!()
    }
}
