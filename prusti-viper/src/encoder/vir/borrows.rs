// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;
use std::collections::HashMap;
use super::ast::Expr;
use prusti_interface::environment::borrowck;

/// The method-unique borrow identifier.
pub type Borrow = borrowck::facts::Loan;

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
    /// This must be a magic wand.
    wand: Expr,
}

impl MagicWandNode {
    /// Get the LHS of the magic wand.
    pub fn lhs(&self) -> &Expr {
        match self.wand {
            Expr::MagicWand(box ref lhs, _) => lhs,
            _ => unreachable!(),
        }
    }
    /// Get the RHS of the magic wand.
    pub fn rhs(&self) -> &Expr {
        match self.wand {
            Expr::MagicWand(_, box ref rhs) => rhs,
            _ => unreachable!(),
        }
    }
}

/// The type of the reborrowing DAG node.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum NodeKind {
    /// See description of `NodeMove`.
    Move(MoveNode),
    /// See description of `MagicWandNode`.
    MagicWand(MagicWandNode),
}

/// Node of the reborrowing DAG.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Node {
    pub borrow: Borrow,
    pub reborrowing_nodes: Vec<Borrow>,
    pub reborrowed_nodes: Vec<Borrow>,
    pub kind: NodeKind,
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            NodeKind::Move(_) => {
                write!(f, "Move({:?})", self.borrow)
            }
            NodeKind::MagicWand(_) => {
                write!(f, "MagicWand({:?})", self.borrow)
            }
        }
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
    pub fn add_move_node(
        &mut self,
        borrow: Borrow,
        reborrowing_nodes: &[Borrow],
        reborrowed_nodes: &[Borrow],
        src: Expr,
        dest: Expr,
    ) {
        let new_index = self.dag.nodes.len();
        assert!(!self.dag.borrow_indices.contains_key(&borrow));
        let node = Node {
            borrow: borrow,
            reborrowing_nodes: reborrowing_nodes.into(),
            reborrowed_nodes: reborrowed_nodes.into(),
            kind: NodeKind::Move(MoveNode {
                src: src,
                dest: dest,
            }),
        };
        self.dag.nodes.push(node);
    }
    pub fn finish(self) -> DAG {
        self.dag
    }
}

impl fmt::Debug for DAG {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ReborrowingDAG")
    }
}

impl fmt::Display for DAG {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ReborrowingDAG")
    }
}
