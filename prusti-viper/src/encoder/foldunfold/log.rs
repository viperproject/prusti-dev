// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! The log keeps track of actions performed by the fold-unfold algorithm so that they can be
//! undone when restoring borrowed permissions.

use encoder::vir;
use encoder::foldunfold::action::Action;
use encoder::foldunfold::perm::Perm;
use std::collections::HashMap;
use std::cmp::Ordering;
use std::iter;


/// The type of the access permission.
#[derive(Clone, Copy, Eq, PartialEq, Hash)]
enum PermType {
    /// Field access predicate.
    FieldAccess,
    /// Predicate access predicate.
    PredicateAccess,
}

#[derive(Clone)]
pub(super) struct EventLog {
    /// Actions performed by the fold-unfold algorithm before the join. We can use a single
    /// CfgBlockIndex because fold-unfold algorithms generates a new basic block for dropped
    /// permissions.
    prejoin_actions: HashMap<vir::CfgBlockIndex, Vec<Action>>,

    /// A list of accessibility predicates for which we inhaled `Read`
    /// permission when creating a borrow and original places from which
    /// they borrow.
    duplicated_reads: HashMap<vir::borrows::Borrow, Vec<(vir::Expr, vir::Expr, u32)>>,

    /// The place that is blocked by a given borrow.
    blocked_place: HashMap<vir::borrows::Borrow, vir::Expr>,

    /// A list of accessibility predicates that were converted from
    /// `Write` to `Read` when creating a borrow.
    converted_to_read_places: HashMap<vir::borrows::Borrow, Vec<vir::Expr>>,

    /// A generator of unique IDs.
    id_generator: u32,
}

impl EventLog {
    pub fn new() -> Self {
        Self {
            prejoin_actions: HashMap::new(),
            duplicated_reads: HashMap::new(),
            blocked_place: HashMap::new(),
            converted_to_read_places: HashMap::new(),
            id_generator: 0,
        }
    }
    pub fn log_prejoin_action(&mut self, block_index: vir::CfgBlockIndex, action: Action) {
        let entry = self.prejoin_actions.entry(block_index).or_insert(Vec::new());
        entry.push(action);
    }
    pub fn collect_dropped_permissions(
        &self,
        path: &[vir::CfgBlockIndex],
        dag: &vir::borrows::DAG
    ) -> Vec<Perm> {
        assert!(path.len() > 0);
        let relevant_path = &path[0..path.len()-1];
        let mut dropped_permissions = Vec::new();
        for curr_block_index in relevant_path {
            if let Some(actions) = self.prejoin_actions.get(curr_block_index) {
                for action in actions {
                    if let Action::Drop(perm) = action {
                        if dag.in_borrowed_places(perm.get_place()) {
                            dropped_permissions.push(perm.clone());
                        }
                    }
                }
            }
        }
        dropped_permissions
    }
    /// `perm` is an instance of either `PredicateAccessPredicate` or `FieldAccessPredicate`.
    pub fn log_read_permission_duplication(
        &mut self,
        borrow: vir::borrows::Borrow,
        perm: vir::Expr,
        original_place: vir::Expr,
    ) {
        let entry = self.duplicated_reads.entry(borrow).or_insert(Vec::new());
        entry.push((perm, original_place, self.id_generator));
        self.id_generator += 1;
    }
    pub fn get_duplicated_read_permissions(
        &self,
        borrow: vir::borrows::Borrow
    ) -> Vec<(vir::Expr, vir::Expr)> {
        let mut result = self.duplicated_reads.get(&borrow).cloned().unwrap_or(Vec::new());
        result.sort_by(|(access1, _, id1), (access2, _, id2)| {
            match (access1, access2) {
                (vir::Expr::PredicateAccessPredicate(_, _, _, _),
                 vir::Expr::PredicateAccessPredicate(_, _, _, _)) => {
                    Ordering::Equal
                },
                (vir::Expr::PredicateAccessPredicate(_, _, _, _),
                 vir::Expr::FieldAccessPredicate(_, _, _)) => {
                    Ordering::Less
                },
                (vir::Expr::FieldAccessPredicate(_, _, _),
                 vir::Expr::PredicateAccessPredicate(_, _, _, _)) => {
                    Ordering::Greater
                },
                (vir::Expr::FieldAccessPredicate(box ref place1, _, _),
                 vir::Expr::FieldAccessPredicate(box ref place2, _, _)) => {
                    if place1.has_prefix(place2) {
                        Ordering::Less
                    } else if place2.has_prefix(place1) {
                        Ordering::Greater
                    } else {
                        id1.cmp(id2)
                    }
                },
                x => unreachable!("{:?}", x),
            }
        });
        result.into_iter().map(|(access, original_place, _)| (access, original_place)).collect()
    }
    /// `perm` is an instance of either `PredicateAccessPredicate` or `FieldAccessPredicate`.
    pub fn log_convertion_to_read(
        &mut self,
        borrow: vir::borrows::Borrow,
        perm: vir::Expr
    ) {
        let entry = self.converted_to_read_places.entry(borrow).or_insert(Vec::new());
        entry.push(perm);
    }
    pub fn get_converted_to_read_places(
        &self,
        borrow: vir::borrows::Borrow
    ) -> Vec<vir::Expr> {
        if let Some(accesses) = self.converted_to_read_places.get(&borrow) {
            accesses.clone()
        } else {
            Vec::new()
        }
    }
}
