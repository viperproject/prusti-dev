// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_interface::environment::borrowck::facts::{Loan, PointIndex};
use prusti_rustc_interface::{
    data_structures::fx::{FxHashMap, FxHashSet},
    middle::mir::BasicBlock,
};
use rustc_middle::mir;
use std::{collections::BTreeSet, fmt::Debug, hash::Hash};

/// Simple way to represent a bijection
#[derive(Clone)]
pub struct Bijection<A: Hash, B: Hash> {
    pub fwd: FxHashMap<A, B>,
    pub rev: FxHashMap<A, B>,
}

impl<A: Hash, B: Hash> Default for Bijection<A, B> {
    fn default() -> Self {
        Self {
            fwd: Default::default(),
            rev: Default::default(),
        }
    }
}

impl<A: Hash, B: Hash> Bijection<A, B> {
    pub fn insert(&mut self, a: A, b: B) {
        todo!();
    }

    pub fn remove_a(&mut self, a: A) -> B {
        todo!();
    }

    pub fn remove_b(&mut self, a: A) -> B {
        todo!();
    }
}

pub trait Node = PartialEq + Eq + Debug + Hash;
pub trait Annotation = Eq;

/// Directed graph
#[derive(Hash)]
pub struct DEdge<N: Node> {
    lhs: N,
    rhs: N,
}

pub struct Digraph<N: Node, A: Annotation> {
    nodes: FxHashSet<N>,
    edges: FxHashSet<DEdge<N>>,
    annotation: FxHashMap<DEdge<N>, A>,
}

impl<N: Node, A: Annotation> Digraph<N, A> {
    pub fn new(nodes: FxHashSet<N>, edges: FxHashSet<DEdge<N>>) -> Self {
        Self {
            nodes,
            edges,
            annotation: FxHashMap::default(),
        }
    }
}

/// Directed Hyperedge
#[derive(Debug, PartialEq, Eq, Hash, Clone)]

pub struct DHEdge<N: Node> {
    lhs: BTreeSet<N>,
    rhs: BTreeSet<N>,
}

/// A Hyperdigraph is
///     - A collection of nodes
///     - A collection of directed edges between sets of nodes
/// We assume
///     - The graph is not a multigraph: there are no self-edges, and edges are
///             uniquely identified by their LHS and RHS.
#[derive(Debug, Clone)]
pub struct Hyperdigraph<N: Node> {
    nodes: FxHashSet<N>,
    edges: FxHashSet<DHEdge<N>>,
}

impl<N: Node> Default for Hyperdigraph<N> {
    fn default() -> Self {
        Self {
            nodes: FxHashSet::default(),
            edges: FxHashSet::default(),
        }
    }
}

impl<N: Node> Hyperdigraph<N> {
    pub fn insert_node(&mut self, n: N) {
        assert!(self.nodes.insert(n));
    }

    // In the literature, a directed hyperpath between nodes a and b is a sequence of
    //  directed hyperedges where the intersection beteeen the RHS and LHS of subsequent
    //  hyperedges are nonempty, a is in the LHS of the first hyperpath, and b is in the
    //  RHS of the last hyperpath.

    // While useful, this is not a good notion for loan expiry since it is possible
    //  for a hyperpath to consume some vertex twice: for example
    //              ({x, y} -> {z}), ({x, z} -> {w})
    // is a valid hyperpath between x and w, but is nonsensical as a sequence of
    //  loan expiries. More or less, this is what is implemented in the current
    //  reborrowing DAG code (caveat: this is not a soundess bug in the current implementation,
    //  since it only implements a subclass of hypergraphs:
    //     - The LHS and RHS of loans are tagged MIR places with the same number of projections
    //     - All other hyperedges have |LHS| = |RHS| = 1.
    // This is a fine representation, but is insufficient to represent general coupled
    //  loans, including coupled magic wands).

    // A K-path X->Y in a hypergraph K is a DAG of directed hyperedges, where
    //  - the LHS of each edge in the K-path is contained in the union of RHS's and X
    //  - the RHS of each edge is contained in the union of the LHS's and Y
    //  - For each x in X, y in Y, the K-path contains a hyperpath from x to y

    // For example, in some (sufficiently populated) hypergraph K, the subgraph
    //  {a} -> {b,c,g}
    //  {b,c} -> {e}
    //  {b,c} -> {f}
    // is a K-path {a}->{e,f,g}. It is not a K-path {a,z} -> {e,f,g}, since that violates
    //  the third condition

    // A linear K-path X->Y is a DAG {Ai->Bi}  where {X} disjoint union {Ai}
    //  and {Y} disjoint union {Bi} are equal. The above example is not a linear
    //  K-path.

    pub fn pprint(&self) {
        println!("nodes: {:?}", self.nodes);
        for e in self.edges.iter() {
            println!(" edge: {:?}", e);
        }
    }
}
