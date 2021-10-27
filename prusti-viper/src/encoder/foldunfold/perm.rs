// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::foldunfold::FoldUnfoldError;
use log::trace;
use std::{
    collections::{HashMap, HashSet},
    fmt,
};
use vir_crate::polymorphic::{Expr, PermAmount, Position, Type};

/// An access or predicate permission to a place
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Perm {
    Acc(Expr, PermAmount),
    Pred(Expr, PermAmount),
}

impl Perm {
    pub fn acc(place: Expr, perm_amount: PermAmount) -> Self {
        Perm::Acc(place, perm_amount)
    }

    pub fn pred(place: Expr, perm_amount: PermAmount) -> Self {
        Perm::Pred(place, perm_amount)
    }

    pub fn is_acc(&self) -> bool {
        matches!(self, Perm::Acc(_, _))
    }

    pub fn is_pred(&self) -> bool {
        matches!(self, Perm::Pred(_, _))
    }

    pub fn is_curr(&self) -> bool {
        self.get_place().is_curr()
    }

    pub fn is_local(&self) -> bool {
        self.get_place().is_local()
    }

    pub fn get_type(&self) -> &Type {
        self.get_place().get_type()
    }

    pub fn get_label(&self) -> Option<&String> {
        self.get_place().get_label()
    }

    pub fn get_perm_amount(&self) -> PermAmount {
        match self {
            Perm::Acc(_, p) => *p,
            Perm::Pred(_, p) => *p,
        }
    }

    pub fn get_place(&self) -> &Expr {
        match self {
            &Perm::Acc(ref place, _) | &Perm::Pred(ref place, _) => place,
        }
    }

    pub fn map_place<F>(self, f: F) -> Self
    where
        F: Fn(Expr) -> Expr,
    {
        match self {
            Perm::Acc(place, fr) => Perm::Acc(f(place), fr),
            Perm::Pred(place, fr) => Perm::Pred(f(place), fr),
        }
    }

    pub fn has_proper_prefix(&self, other: &Expr) -> bool {
        self.get_place().has_proper_prefix(other)
    }

    pub fn init_perm_amount(self, new_perm: PermAmount) -> Self {
        trace!("[enter] init_perm_amount({}, {})", self, new_perm);
        assert!(new_perm.is_valid_for_specs());
        match self {
            Perm::Acc(_expr, PermAmount::Remaining) => unreachable!(),
            Perm::Pred(_expr, PermAmount::Remaining) => unreachable!(),
            Perm::Acc(expr, _) => Perm::Acc(expr, new_perm),
            Perm::Pred(expr, _) => Perm::Pred(expr, new_perm),
        }
    }

    pub fn update_perm_amount(self, new_perm: PermAmount) -> Self {
        assert!(self.get_perm_amount().is_valid_for_specs()); // Just a sanity check.
        assert!(new_perm.is_valid_for_specs());
        match self {
            Perm::Acc(expr, _) => Perm::Acc(expr, new_perm),
            Perm::Pred(expr, _) => Perm::Pred(expr, new_perm),
        }
    }

    pub fn set_default_pos(self, pos: Position) -> Self {
        match self {
            Perm::Acc(expr, perm) => Perm::Acc(expr.set_default_pos(pos), perm),
            Perm::Pred(expr, perm) => Perm::Pred(expr.set_default_pos(pos), perm),
        }
    }
}

impl fmt::Display for Perm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Perm::Acc(ref place, perm_amount) => write!(f, "Acc({}, {})", place, perm_amount),
            Perm::Pred(ref place, perm_amount) => write!(f, "Pred({}, {})", place, perm_amount),
        }
    }
}

impl fmt::Debug for Perm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Perm::Acc(ref place, perm_amount) => write!(f, "Acc({:?}, {})", place, perm_amount),
            Perm::Pred(ref place, perm_amount) => write!(f, "Pred({:?}, {})", place, perm_amount),
        }
    }
}

/// A set of permissions
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PermSet {
    acc_perms: HashMap<Expr, PermAmount>,
    pred_perms: HashMap<Expr, PermAmount>,
}

impl PermSet {
    pub fn empty() -> Self {
        PermSet {
            acc_perms: HashMap::new(),
            pred_perms: HashMap::new(),
        }
    }

    /// Corresponds to an `inhale`
    /// Note: the amount of the permission is actually ignored
    pub fn add(&mut self, perm: Perm) {
        match perm {
            Perm::Acc(place, perm_amount) => self.acc_perms.insert(place, perm_amount),
            Perm::Pred(place, perm_amount) => self.pred_perms.insert(place, perm_amount),
        };
    }

    pub fn perms(mut self) -> Vec<Perm> {
        let mut perms = vec![];
        for (place, perm_amount) in self.acc_perms.drain() {
            perms.push(Perm::acc(place, perm_amount));
        }
        for (place, perm_amount) in self.pred_perms.drain() {
            perms.push(Perm::pred(place, perm_amount));
        }
        perms
    }
}

impl fmt::Display for PermSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        let mut first = true;
        for perm in self.clone().perms().iter() {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "{}", perm)?;
        }
        write!(f, "}}")
    }
}

pub trait PermIterator {
    fn collect_curr(&mut self) -> Vec<Perm>;
    fn group_by_label(&mut self) -> HashMap<Option<String>, Vec<Perm>>;
}

impl<T> PermIterator for T
where
    T: Iterator<Item = Perm>,
{
    fn collect_curr(&mut self) -> Vec<Perm> {
        self.filter(|perm| perm.is_curr()).collect()
    }

    fn group_by_label(&mut self) -> HashMap<Option<String>, Vec<Perm>> {
        let mut res_perms = HashMap::new();
        for perm in self {
            res_perms
                .entry(perm.get_label().cloned())
                .or_insert_with(Vec::new)
                .push(perm.clone());
        }
        res_perms
    }
}

/// Note: since this function performs set difference, it does **not**
/// panic if `left` has less permission than `right`.
fn place_perm_difference(
    mut left: HashMap<Expr, PermAmount>,
    mut right: HashMap<Expr, PermAmount>,
) -> HashMap<Expr, PermAmount> {
    for (place, right_perm_amount) in right.drain() {
        if let Some(left_perm_amount) = left.get(&place) {
            match (*left_perm_amount, right_perm_amount) {
                (PermAmount::Read, PermAmount::Read)
                | (PermAmount::Read, PermAmount::Write)
                | (PermAmount::Write, PermAmount::Write) => {
                    left.remove(&place);
                }
                _ => unreachable!("left={} right={}", left_perm_amount, right_perm_amount),
            }
        }
    }
    left
}

/// Set difference that takes into account that removing `x.f` also removes any `x.f.g.h`
pub fn perm_difference(left: HashSet<Perm>, right: HashSet<Perm>) -> HashSet<Perm> {
    trace!(
        "[enter] perm_difference(left={:?}, right={:?})",
        left,
        right
    );
    let left_acc = left.iter().filter(|x| x.is_acc()).cloned();
    let left_pred = left.iter().filter(|x| x.is_pred()).cloned();
    let right_acc = right.iter().filter(|x| x.is_acc()).cloned();
    let right_pred = right.iter().filter(|x| x.is_pred()).cloned();
    let mut res = vec![];
    res.extend(
        place_perm_difference(
            left_acc
                .map(|p| (p.get_place().clone(), p.get_perm_amount()))
                .collect(),
            right_acc
                .map(|p| (p.get_place().clone(), p.get_perm_amount()))
                .collect(),
        )
        .drain()
        .map(|(place, amount)| Perm::Acc(place, amount))
        .collect::<Vec<_>>(),
    );
    res.extend(
        place_perm_difference(
            left_pred
                .map(|p| (p.get_place().clone(), p.get_perm_amount()))
                .collect(),
            right_pred
                .map(|p| (p.get_place().clone(), p.get_perm_amount()))
                .collect(),
        )
        .drain()
        .map(|(place, amount)| Perm::Pred(place, amount))
        .collect::<Vec<_>>(),
    );
    res.into_iter().collect()
}
