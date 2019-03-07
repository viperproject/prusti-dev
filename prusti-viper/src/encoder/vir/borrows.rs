// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;
use std::collections::HashMap;
use super::ast::{Expr, Stmt};
use prusti_interface::environment::borrowck;

/// The method-unique borrow identifier.
pub type Borrow = borrowck::facts::Loan;

/*
/// The borrow that moved permissions from one path to another. To undo it,
/// we need to move all permissions associated with `src` to `dest`
/// in the fold-unfold state.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct MoveNode {
    pub src: Expr,
    pub dest: Expr,
}

/// The borrow that crossed a verification boundary and requires a
/// magic wand. To undo it, we need to apply the given magic wand.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct MagicWandNode {
//  /// This must be a magic wand.
//  wand: Expr,
}
*/

/*
impl MagicWandNode {
    /// Get the LHS of the magic wand.
    pub fn lhs(&self) -> &Expr {
        match self.wand {
            Expr::MagicWand(box ref lhs, _, _) => lhs,
            _ => unreachable!(),
        }
    }
    /// Get the RHS of the magic wand.
    pub fn rhs(&self) -> &Expr {
        match self.wand {
            Expr::MagicWand(_, box ref rhs, _) => rhs,
            _ => unreachable!(),
        }
    }
}
*/

/*
/// The type of the reborrowing DAG node.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum NodeKind {
    /// See description of `NodeMove`.
    Move(MoveNode),
    /// See description of `MagicWandNode`.
    MagicWand(MagicWandNode),
}
*/

/// Node of the reborrowing DAG.
#[derive(Clone, PartialEq, Eq)]
pub struct Node {
    /// This borrow occurred iff `guard` is `true`.
    pub guard: Expr,
    pub borrow: Borrow,
    pub reborrowing_nodes: Vec<Borrow>,
    pub reborrowed_nodes: Vec<Borrow>,
    //pub kind: NodeKind,
    pub stmts: Vec<Stmt>
}

impl Node {
    //pub fn new_move_node(
        //guard: Expr,
        //borrow: Borrow,
        //reborrowing_nodes: Vec<Borrow>,
        //reborrowed_nodes: Vec<Borrow>,
        //src: Expr,
        //dest: Expr,
    //) -> Self {
        //Self {
            //guard,
            //borrow,
            //reborrowing_nodes,
            //reborrowed_nodes,
            //kind: NodeKind::Move(MoveNode {
                //src: src,
                //dest: dest,
            //}),
            //stmts: Vec::new(),  // TODO: Fix.
        //}
    //}
    pub fn new(
        guard: Expr,
        borrow: Borrow,
        reborrowing_nodes: Vec<Borrow>,
        reborrowed_nodes: Vec<Borrow>,
        stmts: Vec<Stmt>,
    ) -> Self {
        Self {
            guard,
            borrow,
            reborrowing_nodes,
            reborrowed_nodes,
            stmts,
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
#[derive(Clone, PartialEq, Eq)]
pub struct DAG {
    /// Mapping from borrows to their node indices.
    borrow_indices: HashMap<Borrow, usize>,
    nodes: Vec<Node>,
}

impl DAG {
    pub fn iter(&self) -> impl Iterator<Item=&Node> {
        self.nodes.iter()
    }
    pub fn get_borrow_index(&self, borrow: Borrow) -> usize {
        trace!("get_borrow_index(borrow={:?})", borrow);
        self.borrow_indices[&borrow]
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
        }
        trace!("[exit] check_integrity dag=[{:?}]", self);
    }
    //pub fn get_location(node: Node) -> Location { ... }
}

/// A struct for constructing the reborrowing DAG.
pub struct DAGBuilder {
    dag: DAG,
}

impl DAGBuilder {
    pub fn new() -> Self {
        let dag = DAG {
            borrow_indices: HashMap::new(),
            nodes: Vec::new(),
        };
        Self {
            dag: dag,
        }
    }
    pub fn add_node(&mut self, node: Node) {
        let borrow = node.borrow;
        let new_index = self.dag.nodes.len();
        assert!(!self.dag.borrow_indices.contains_key(&borrow));
        self.dag.borrow_indices.insert(borrow, new_index);
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
