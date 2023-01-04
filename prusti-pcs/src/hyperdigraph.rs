// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};
use std::{collections::BTreeSet, fmt::Debug, hash::Hash};

pub trait Bijectable = Eq + Hash + Debug + Clone;

/// Simple way to represent a bijection
#[derive(Clone)]
pub struct Bijection<A: Bijectable, B: Bijectable> {
    pub fwd: FxHashMap<A, B>,
    pub rev: FxHashMap<B, A>,
}

impl<A: Bijectable, B: Bijectable> Default for Bijection<A, B> {
    fn default() -> Self {
        Self {
            fwd: Default::default(),
            rev: Default::default(),
        }
    }
}

impl<A: Bijectable, B: Bijectable> Bijection<A, B> {
    pub fn insert(&mut self, a: A, b: B) {
        assert!(None == self.fwd.insert(a.clone(), b.clone()));
        assert!(None == self.rev.insert(b.clone(), a.clone()));
    }

    pub fn remove_a(&mut self, a: &A) -> Option<B> {
        let b = self.fwd.remove(a)?;
        assert!(self.rev.remove(&b) != None);
        Some(b)
    }

    #[allow(unused)]
    pub fn remove_b(&mut self, _: &A) -> B {
        todo!();
    }
    pub fn get_fwd(&self, a: &A) -> Option<&B> {
        self.fwd.get(a)
    }

    #[allow(unused)]
    pub fn pprint(&self) {
        for (k, v) in self.fwd.iter() {
            println!("\t** {:?} <-> {:?} ", k, v);
        }
    }

    pub fn replace_a(&mut self, a: A, a1: A) {
        todo!();
    }
}

pub trait Node = PartialEq + Eq + Debug + Hash + Ord + Clone;
pub trait Annotation = Eq;

/// Directed graph
#[derive(Hash)]
pub struct DEdge<N: Node> {
    lhs: N,
    rhs: N,
}

#[allow(unused)]
pub struct Digraph<N: Node, A: Annotation> {
    nodes: FxHashSet<N>,
    edges: FxHashSet<DEdge<N>>,
    annotation: FxHashMap<DEdge<N>, A>,
}

#[allow(unused)]
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
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]

pub struct DHEdge<N: Node> {
    pub lhs: BTreeSet<N>,
    pub rhs: BTreeSet<N>,
}

impl<N: Node> DHEdge<N> {
    pub fn replace_lhs(&mut self, from: &BTreeSet<N>, to: &BTreeSet<N>) {
        if from.is_subset(&self.lhs) {
            self.lhs = self.lhs.difference(from).cloned().collect();
            self.lhs = self.lhs.union(to).cloned().collect();
        }
    }

    pub fn replace_rhs(&mut self, from: &BTreeSet<N>, to: &BTreeSet<N>) {
        if from.is_subset(&self.rhs) {
            self.rhs = self.rhs.difference(from).cloned().collect();
            self.rhs = self.rhs.union(to).cloned().collect();
        }
    }
}

/// A Hyperdigraph is
///     - A collection of nodes
///     - A collection of directed edges between sets of nodes
/// We assume
///     - The graph is not a multigraph: there are no self-edges, and edges are
///             uniquely identified by their LHS and RHS.
#[derive(Debug, Clone)]
pub struct Hyperdigraph<N: Node> {
    nodes: BTreeSet<N>,
    edges: BTreeSet<DHEdge<N>>,
}

impl<N: Node> Default for Hyperdigraph<N> {
    fn default() -> Self {
        Self {
            nodes: Default::default(),
            edges: Default::default(),
        }
    }
}

impl<N: Node> Hyperdigraph<N> {
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty() && self.edges.is_empty()
    }

    pub fn nodes(&self) -> &BTreeSet<N> {
        &self.nodes
    }

    pub fn edges(&self) -> &BTreeSet<DHEdge<N>> {
        &self.edges
    }

    /// Mutate all edges, also update a bijection
    /// Really slow function, and incorrect seperation of concerns wrt. the bijection.
    pub fn replace_in_all_nodes<X: Bijectable>(
        &mut self,
        from: &BTreeSet<N>,
        to: &BTreeSet<N>,
        edge_labels: &mut Bijection<DHEdge<N>, BTreeSet<X>>,
    ) {
        // This is a really bad way to do this, but BTreeSets don't have mutable iterators.
        // A (sligtly) better way might be to only move out and back in the edges which need to be changed.
        let owned_edges = std::mem::replace(&mut self.edges, BTreeSet::new());
        for mut e in owned_edges.into_iter() {
            let bij_rhs = (*edge_labels.get_fwd(&e).unwrap()).clone();
            edge_labels.remove_a(&e).unwrap();
            e.replace_lhs(from, to);
            e.replace_rhs(from, to);
            edge_labels.insert(e.clone(), bij_rhs);
            self.edges.insert(e);
        }
    }

    // pub fn mut_edges(&mut self) -> &mut BTreeSet<DHEdge<N>> {
    //     &mut self.edges
    // }

    pub fn include_edge(&mut self, e: DHEdge<N>) {
        // Ensure that all nodes required by the edge are included in the graph
        for n in e.lhs.iter().chain(e.rhs.iter()) {
            self.include_node(n);
        }
        // Add the edge, if it doesn't exist.
        if !self.edges.contains(&e) {
            self.insert_edge(e);
        }
    }

    // This is a hack and (fixme) should be removed
    pub fn cleanup_nodes(&mut self) {
        let all_lhs = self
            .edges
            .iter()
            .map(|e| (*e).lhs.clone())
            .flatten()
            .collect::<BTreeSet<_>>();

        let all_rhs = self
            .edges
            .iter()
            .map(|e| (*e).rhs.clone())
            .flatten()
            .collect::<BTreeSet<_>>();

        self.nodes
            .retain(|n| all_lhs.contains(n) || all_rhs.contains(n));
    }

    pub fn remove_edge(&mut self, e: &DHEdge<N>) {
        self.edges.remove(e);
        let mut dirty_nodes: BTreeSet<_> = e.lhs.union(&e.rhs).cloned().collect();
        // Silly to do this but make prototyping easier
        for se in self.edges.iter() {
            for l in se.lhs.iter() {
                dirty_nodes.remove(l);
            }
            for r in se.rhs.iter() {
                dirty_nodes.remove(r);
            }
        }
        for d in dirty_nodes.iter() {
            self.nodes.remove(d);
        }
    }

    /// Include an edge which doesn't exist, with nodes that do exist.
    fn insert_edge(&mut self, e: DHEdge<N>) {
        assert!(e.lhs.is_subset(&self.nodes));
        assert!(e.rhs.is_subset(&self.nodes));
        assert!(self.edges.insert(e))
    }

    /// Include a node that might exist
    fn include_node(&mut self, n: &N) {
        if !self.nodes.contains(n) {
            self.insert_node(n.clone());
        }
    }

    /// Include a node that doesn't exist
    pub fn insert_node(&mut self, n: N) {
        assert!(self.nodes.insert(n));
    }

    /// Remove a node that does exist exist
    pub fn remove_node(&mut self, n: &N) {
        assert!(self.nodes.remove(n));
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

    #[allow(unused)]
    pub fn find_affine_path(
        &self,
        from: &BTreeSet<N>,
        to: &BTreeSet<N>,
    ) -> Option<BTreeSet<DHEdge<N>>> {
        // Brute force, stupid, recursive algorithm
        // Also, I'm pretty sure this breaks on cycles... though are they K-paths?
        if from.is_subset(to) {
            return Some(BTreeSet::new());
        }
        for next_edge in self.hyper_successor(from) {
            let next_from: BTreeSet<_> = from
                .difference(&next_edge.lhs)
                .cloned()
                .collect::<BTreeSet<_>>()
                .union(&next_edge.rhs)
                .cloned()
                .collect();
            if let Some(mut result) = self.find_affine_path(&next_from, to) {
                assert!(result.insert(next_edge));
                return Some(result);
            }
        }

        return None;
    }

    /// REQUIRES: edges is acyclic and an affine path
    /// U{LHS's} U RHS = U{RHS's} U LHS
    /// It also can't include any other named edges, for now that means no other edges (under mut assumption)
    /// Return the edge
    pub fn collapse_acyclic_affine_path(&self, edges: &BTreeSet<DHEdge<N>>) -> DHEdge<N> {
        if edges.len() == 0 {
            panic!("Internal error (affine hull of size zero");
        }
        let mut lhs: BTreeSet<N> = BTreeSet::default();
        let mut rhs: BTreeSet<N> = BTreeSet::default();
        for e in edges.iter() {
            lhs = lhs.union(&e.lhs).cloned().collect();
            rhs = rhs.union(&e.rhs).cloned().collect();
        }
        DHEdge {
            lhs: rhs.difference(&lhs).cloned().collect::<BTreeSet<_>>(),
            rhs: lhs.difference(&rhs).cloned().collect::<BTreeSet<_>>(),
        }
    }

    #[allow(unused)]
    // Find all edges whose LHS is a subset of "nodes"
    fn hyper_successor(&self, nodes: &BTreeSet<N>) -> Vec<DHEdge<N>> {
        self.edges
            .iter()
            .filter(|e| e.lhs.is_subset(nodes))
            .cloned()
            .collect()
    }

    pub fn pprint_with_annotations<T: Bijectable>(&self, ann: &Bijection<DHEdge<N>, T>) {
        println!("\t** nodes: {:?}", self.nodes);
        for e in self.edges.iter() {
            println!("\t * edge: {:?}\t({:?})", e, ann.get_fwd(&e));
        }
    }

    /// Replace one node with another.
    /// Panics if the from node does not exist or the to node already exists.
    pub fn replace_nodes<X: Bijectable>(
        &mut self,
        from: N,
        to: N,
        edge_labels: &mut Bijection<DHEdge<N>, BTreeSet<X>>,
    ) {
        // Update the nodes
        self.remove_node(&from);
        self.insert_node(to.clone());

        // Update the edges
        // fixme: slow hack
        let owned_edges = std::mem::replace(&mut self.edges, BTreeSet::new());
        for mut e in owned_edges.into_iter() {
            let bij_rhs = (*edge_labels.get_fwd(&e).unwrap()).clone();
            edge_labels.remove_a(&e).unwrap();
            if e.lhs.remove(&from) {
                assert!(e.lhs.insert(to.clone()));
            }
            if e.rhs.remove(&from) {
                assert!(e.rhs.insert(to.clone()));
            }
            edge_labels.insert(e.clone(), bij_rhs);
            self.edges.insert(e);
        }
    }
}
