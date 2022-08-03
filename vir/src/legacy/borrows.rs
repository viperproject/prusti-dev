// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::ast::{Expr, ExprIterator, Stmt};
use log::{debug, trace};
use std::{
    collections::{HashMap, VecDeque},
    fmt,
};

/// The method-unique borrow identifier.
#[derive(
    Ord, PartialOrd, Eq, PartialEq, Clone, Copy, Hash, serde::Serialize, serde::Deserialize,
)]
pub struct Borrow(pub(crate) usize);

impl From<usize> for Borrow {
    fn from(index: usize) -> Borrow {
        Borrow(index)
    }
}

impl From<Borrow> for usize {
    fn from(borrow: Borrow) -> Self {
        borrow.0 as usize
    }
}

impl fmt::Debug for Borrow {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "L{}", self.0)
    }
}

pub fn borrow_id(borrow: Borrow) -> usize {
    borrow.into()
}

/// Node of the reborrowing DAG.
#[derive(Clone, PartialEq, Eq)]
pub struct Node {
    /// The basic block at which the borrow occured was executed only
    /// iff the `guard` is true.
    pub guard: Expr,
    pub borrow: Borrow,
    pub reborrowing_nodes: Vec<Borrow>,
    pub reborrowed_nodes: Vec<Borrow>,
    pub stmts: Vec<Stmt>,
    /// Places that were borrowed and should be kept in fold/unfold.
    pub borrowed_places: Vec<Expr>,
    /// Borrows that are borrowing the same place.
    pub conflicting_borrows: Vec<Borrow>,
    pub alive_conflicting_borrows: Vec<Borrow>,
    /// The place (potentially old) through which the permissions can
    /// still be accessed even if the loan was killed.
    pub place: Option<Expr>,
}

impl Node {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        guard: Expr,
        borrow: Borrow,
        reborrowing_nodes: Vec<Borrow>,
        reborrowed_nodes: Vec<Borrow>,
        stmts: Vec<Stmt>,
        borrowed_places: Vec<Expr>,
        conflicting_borrows: Vec<Borrow>,
        alive_conflicting_borrows: Vec<Borrow>,
        place: Option<Expr>,
    ) -> Self {
        Self {
            guard,
            borrow,
            reborrowing_nodes,
            reborrowed_nodes,
            stmts,
            borrowed_places,
            conflicting_borrows,
            alive_conflicting_borrows,
            place,
        }
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.borrow)
    }
}

/// Reborrowing directed acyclic graph (DAG). It should not be mutated
/// after it is constructed. For construction use `DAGBuilder`.
#[derive(Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize, Default)]
pub struct DAG {
    /// Mapping from borrows to their node indices.
    #[serde(skip)]
    pub(crate) borrow_indices: HashMap<Borrow, usize>,
    #[serde(skip)]
    pub(crate) nodes: Vec<Node>,
    #[serde(skip)]
    pub(crate) borrowed_places: Vec<Expr>,
}

impl DAG {
    pub fn iter(&self) -> impl Iterator<Item = &Node> {
        self.nodes.iter()
    }
    pub fn get_borrow_index(&self, borrow: Borrow) -> usize {
        trace!("get_borrow_index(borrow={:?})", borrow);
        self.borrow_indices[&borrow]
    }
    pub fn in_borrowed_places(&self, place: &Expr) -> bool {
        self.borrowed_places
            .iter()
            .any(|borrowed_place| place.has_prefix(borrowed_place))
    }
    pub fn check_integrity(&self) {
        trace!("[enter] check_integrity dag=[{:?}]", self);
        if let Some(first) = self.nodes.first() {
            assert!(first.reborrowing_nodes.is_empty());
        }
        if let Some(last) = self.nodes.last() {
            assert!(last.reborrowed_nodes.is_empty());
        }
        assert!(self.nodes.len() == self.borrow_indices.len());
        for (i, node) in self.nodes.iter().enumerate() {
            assert!(self.borrow_indices[&node.borrow] == i);
            for borrow in &node.reborrowing_nodes {
                assert!(self.borrow_indices.contains_key(borrow), "{:?}", borrow);
            }
            for borrow in &node.reborrowed_nodes {
                assert!(self.borrow_indices.contains_key(borrow), "{:?}", borrow);
            }
            for place in &node.borrowed_places {
                debug!("{:?}: {}", node.borrow, place);
            }
        }
        trace!("[exit] check_integrity dag=[{:?}]", self);
    }
    /// Get the complete guard for the given node.
    pub fn guard(&self, expiring_borrow: Borrow) -> Expr {
        let index = self.get_borrow_index(expiring_borrow);
        let mut guard_indices = vec![index];
        let mut to_visit = VecDeque::new();
        let mut visited = vec![false; self.nodes.len()];
        to_visit.push_back(index);
        visited[index] = true;
        while let Some(curr_index) = to_visit.pop_front() {
            let curr_node = &self.nodes[curr_index];
            for borrow in &curr_node.reborrowing_nodes {
                let borrow_index = self.borrow_indices[borrow];
                if !visited[borrow_index] {
                    to_visit.push_back(borrow_index);
                    visited[borrow_index] = true;
                    guard_indices.push(borrow_index);
                }
            }
        }
        guard_indices
            .into_iter()
            .map(|index| self.nodes[index].guard.clone())
            .conjoin()
    }
}

/// A struct for constructing the reborrowing DAG.
#[derive(Default)]
pub struct DAGBuilder {
    dag: DAG,
}

impl DAGBuilder {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn add_node(&mut self, node: Node) {
        let borrow = node.borrow;
        let new_index = self.dag.nodes.len();
        assert!(!self.dag.borrow_indices.contains_key(&borrow));
        self.dag.borrow_indices.insert(borrow, new_index);
        for place in &node.borrowed_places {
            self.dag.borrowed_places.push(place.clone());
        }
        self.dag.nodes.push(node);
    }
    pub fn finish(self) -> DAG {
        self.dag.check_integrity();
        self.dag
    }
}

impl fmt::Debug for DAG {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ReborrowingDAG(")?;
        for node in &self.nodes {
            write!(f, "{:?},", node.borrow)?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for DAG {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ReborrowingDAG")
    }
}
