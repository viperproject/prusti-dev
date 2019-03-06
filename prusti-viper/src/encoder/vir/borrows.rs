// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;
use super::ast::Expr;
use prusti_interface::environment::borrowck;

/// The method-unique borrow identifier.
pub type Borrow = borrowck::facts::Loan;

/// The borrow that moved permissions from one path to another. To undo it,
/// we need to move all permissions associated with `src` to `dest`
/// in the fold-unfold state.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct MoveNode {
    borrow: Borrow,
    src: Expr,
    dest: Expr,
}

/// The borrow that crossed a verification boundary and requires a
/// magic wand. To undo it, we need to apply the given magic wand.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct MagicWandNode {
    borrow: Borrow,
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
    /// The root of the reborrowing DAG. Is used to mark the “location”
    /// where the borrows expired.
    Root,
    /// See description of `NodeMove`.
    Move(MoveNode),
    /// See description of `MagicWandNode`.
    MagicWand(MagicWandNode),
}

/// Node of the reborrowing DAG.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Node {
    kind: NodeKind,

}

/// Reborrowing directed acyclic graph (DAG).
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct DAG {
    nodes: Vec<Node>,
}

impl DAG {
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
        }
    }
    //pub fn get_location(node: Node) -> Location { ... }
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
