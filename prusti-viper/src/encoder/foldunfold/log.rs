// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! The log keeps track of actions performed by the fold-unfold algorithm so that they can be
//! undone when restoring borrowed permissions.

use crate::encoder::foldunfold::{action::Action, perm::Perm, FoldUnfoldError};
use log::trace;
use prusti_common::utils::to_string::ToString;
use rustc_hash::FxHashMap;
use std::{cmp::Ordering, fmt::Write, rc::Rc, sync::RwLock};
use vir_crate::polymorphic as vir;

// Note: Now every PathCtxt has its own EventLog, because a Borrow no longer unique
// (e.g. we duplicate the evaluation of the loop condition in the encoding of loops).
// The idea is to progressively transform this *log* into a *state*, removing past actions that are
// no longer needed.
#[derive(Clone, Debug)]
pub(super) struct EventLog {
    /// Actions performed by the fold-unfold algorithm before the join. We can use a single
    /// CfgBlockIndex because fold-unfold algorithms generates a new basic block for dropped
    /// permissions.
    prejoin_actions: FxHashMap<vir::CfgBlockIndex, Rc<RwLock<Vec<Action>>>>,

    /// A list of accessibility predicates for which we inhaled `Read`
    /// permission when creating a borrow and original places from which
    /// they borrow.
    ///
    /// The tuples values:
    ///
    /// 1.  The access predicate.
    /// 2.  The rhs of the assignment that created this borrow.
    /// 3.  A unique number.
    duplicated_reads: FxHashMap<vir::borrows::Borrow, Vec<(vir::Expr, vir::Expr, u32)>>,

    /// The place that is blocked by a given borrow.
    blocked_place: FxHashMap<vir::borrows::Borrow, vir::Expr>,

    /// A list of accessibility predicates that were converted from
    /// `Write` to `Read` when creating a borrow.
    converted_to_read_places: FxHashMap<vir::borrows::Borrow, Vec<vir::Expr>>,

    /// A generator of unique IDs.
    id_generator: u32,
}

impl EventLog {
    pub fn new() -> Self {
        Self {
            prejoin_actions: FxHashMap::default(),
            duplicated_reads: FxHashMap::default(),
            blocked_place: FxHashMap::default(),
            converted_to_read_places: FxHashMap::default(),
            id_generator: 0,
        }
    }

    #[tracing::instrument(level = "trace", skip_all, fields(block_index = %block_index, action = %action))]
    pub fn log_prejoin_action(&mut self, block_index: vir::CfgBlockIndex, action: Action) {
        let entry_rc = self
            .prejoin_actions
            .entry(block_index)
            .or_insert_with(|| Rc::new(RwLock::new(Vec::new())));
        let mut entry = entry_rc.write().unwrap();
        entry.push(action);
        trace!("[exit] log_prejoin_action {}", entry.iter().to_string());
    }

    pub fn collect_dropped_permissions(
        &self,
        path: &[vir::CfgBlockIndex],
        dag: &vir::borrows::DAG,
    ) -> Vec<Perm> {
        assert!(!path.is_empty());
        let relevant_path = &path[0..path.len() - 1];
        let mut dropped_permissions = Vec::new();
        for curr_block_index in relevant_path {
            if let Some(actions) = self.prejoin_actions.get(curr_block_index) {
                let actions_read = actions.read().unwrap();
                let actions_iter = actions_read.iter();
                for action in actions_iter {
                    if let Action::Drop(perm, missing_perm) = action {
                        if dag.in_borrowed_places(missing_perm.get_place()) {
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
        let entry = self.duplicated_reads.entry(borrow).or_default();
        entry.push((perm, original_place, self.id_generator));
        self.id_generator += 1;
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn get_duplicated_read_permissions(
        &self,
        borrow: vir::borrows::Borrow,
    ) -> Vec<(vir::Expr, vir::Expr)> {
        let mut result = self
            .duplicated_reads
            .get(&borrow)
            .cloned()
            .unwrap_or_default();
        result.sort_unstable_by(
            |(access1, _, id1), (access2, _, id2)| match (access1, access2) {
                (
                    vir::Expr::PredicateAccessPredicate(..),
                    vir::Expr::PredicateAccessPredicate(..),
                ) => Ordering::Equal,
                (vir::Expr::PredicateAccessPredicate(..), vir::Expr::FieldAccessPredicate(..)) => {
                    Ordering::Less
                }
                (vir::Expr::FieldAccessPredicate(..), vir::Expr::PredicateAccessPredicate(..)) => {
                    Ordering::Greater
                }
                (
                    vir::Expr::FieldAccessPredicate(vir::FieldAccessPredicate {
                        base: box ref place1,
                        ..
                    }),
                    vir::Expr::FieldAccessPredicate(vir::FieldAccessPredicate {
                        base: box ref place2,
                        ..
                    }),
                ) => {
                    let key1 = (place1.place_depth(), id1);
                    let key2 = (place2.place_depth(), id2);
                    key2.cmp(&key1)
                }
                x => unreachable!("{:?}", x),
            },
        );
        trace!(
            "[exit] get_duplicated_read_permissions({:?}) = {}",
            borrow,
            result.iter().fold(String::new(), |mut output, (a, p, id)| {
                let _ = write!(output, "({a}, {p}, {id}), ");
                output
            })
        );
        result
            .into_iter()
            .map(|(access, original_place, _)| (access, original_place))
            .collect()
    }

    /// `perm` is an instance of either `PredicateAccessPredicate` or `FieldAccessPredicate`.
    pub fn log_convertion_to_read(&mut self, borrow: vir::borrows::Borrow, perm: vir::Expr) {
        assert!(perm.get_perm_amount() == vir::PermAmount::Remaining);
        let entry = self.converted_to_read_places.entry(borrow).or_default();
        entry.push(perm);
    }

    pub fn get_converted_to_read_places(&self, borrow: vir::borrows::Borrow) -> Vec<vir::Expr> {
        if let Some(accesses) = self.converted_to_read_places.get(&borrow) {
            accesses.clone()
        } else {
            Vec::new()
        }
    }

    pub fn log_borrow_expiration(&mut self, borrow: vir::borrows::Borrow) {
        self.duplicated_reads.remove(&borrow);
        self.blocked_place.remove(&borrow);
        self.converted_to_read_places.remove(&borrow);
    }

    /// Join `other` into `self`
    pub(super) fn join(&mut self, mut other: Self) -> Result<(), FoldUnfoldError> {
        for (other_key, other_value) in other.prejoin_actions.drain() {
            self.prejoin_actions.entry(other_key).or_insert(other_value);
        }
        // FIXME: This is not enough if the same borrow is created in two different paths
        for (other_key, other_value) in other.duplicated_reads.drain() {
            self.duplicated_reads
                .entry(other_key)
                .or_insert(other_value);
        }
        // FIXME: This is not enough if the same borrow is created in two different paths
        for (other_key, other_value) in other.blocked_place.drain() {
            self.blocked_place.entry(other_key).or_insert(other_value);
        }
        // FIXME: This is not enough if the same borrow is created in two different paths
        for (other_key, other_value) in other.converted_to_read_places.drain() {
            self.converted_to_read_places
                .entry(other_key)
                .or_insert(other_value);
        }
        self.id_generator = self.id_generator.max(other.id_generator);
        Ok(())
    }
}
