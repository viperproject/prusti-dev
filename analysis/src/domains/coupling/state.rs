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
pub struct CouplingState<'facts, 'mir: 'facts, 'tcx: 'mir> {
    coupling_graph: CDG<'tcx>,
    mir: &'mir BodyWithBorrowckFacts<'tcx>,
    fact_table: &'facts FactTable<'tcx>,
}

impl<'facts, 'mir: 'facts, 'tcx: 'mir> CouplingState<'facts, 'mir, 'tcx> {
    pub fn check_invariant(&self, location: impl fmt::Debug) -> bool {
        todo!("check the Polonius invariants and determine if they hold")
    }

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

    /// The main inference algorithm for the CDG
    /// Unclear if polonius inference is supposed to be different for Start and Mid locations yet
    fn apply_cdg_inference(&mut self, location: Location) -> AnalysisResult<()> {
        println!("[inference]   enter {:?}", RichLocation::Start(location));
        self.apply_polonius_inference(RichLocation::Start(location))?;
        println!("[inference]   enter {:?}", RichLocation::Mid(location));
        self.apply_polonius_inference(RichLocation::Mid(location))?;
        Ok(())
    }

    fn apply_polonius_inference(&mut self, location: RichLocation) -> AnalysisResult<()> {
        // todo: inference algorithm
        // if loan_issues.len() > 0 {
        //     println!("[inference]   loan_issues {:?}", loan_issues);
        // }
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
