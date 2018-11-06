// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use encoder::vir::Frac;
use std::fmt;
use std::iter::FlatMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::hash_set;
use std::ops::Mul;

/// An access or predicate permission to a place
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Perm {
    Acc(vir::Place, Frac),
    Pred(vir::Place, Frac)
}

impl Perm {
    pub fn acc(place: vir::Place, frac: Frac) -> Self {
        Perm::Acc(place, frac)
    }

    pub fn pred(place: vir::Place, frac: Frac) -> Self {
        Perm::Pred(place, frac)
    }

    pub fn is_acc(&self) -> bool {
        match self {
            Perm::Acc(_, _) => true,
            _ => false,
        }
    }

    pub fn is_pred(&self) -> bool {
        match self {
            Perm::Pred(_, _) => true,
            _ => false,
        }
    }

    pub fn is_curr(&self) -> bool {
        self.get_place().is_curr()
    }

    pub fn is_base(&self) -> bool {
        self.get_place().is_base()
    }

    pub fn has_old(&self) -> bool {
        self.get_place().has_old()
    }

    pub fn get_pred(&self) -> Option<&vir::Place> {
        match self {
            Perm::Pred(ref place, _) => Some(place),
            _ => None,
        }
    }

    pub fn typed_ref_name(&self) -> Option<String> {
        self.get_place().typed_ref_name()
    }

    pub fn get_type(&self) -> &vir::Type {
        self.get_place().get_type()
    }

    pub fn get_label(&self) -> Option<&String> {
        self.get_place().get_label()
    }

    pub fn get_frac(&self) -> Frac {
        match self {
            Perm::Acc(_, f) => *f,
            Perm::Pred(_, f) => *f,
        }
    }

    pub fn get_place(&self) -> &vir::Place {
        match self {
            &Perm::Acc(ref place, _) |
            &Perm::Pred(ref place, _) => place,
        }
    }

    pub fn place_as_mut_ref(&mut self) -> &mut vir::Place {
        match self {
            &mut Perm::Acc(ref mut place, _) |
            &mut Perm::Pred(ref mut place, _) => place,
        }
    }

    pub fn unwrap_place(self) -> vir::Place {
        match self {
            Perm::Acc(place, _) |
            Perm::Pred(place, _) => place,
        }
    }

    pub fn map_place<F>(self, f: F) -> Self
        where F: Fn(vir::Place) -> vir::Place
    {
        match self {
            Perm::Acc(place, fr) => Perm::Acc(f(place), fr),
            Perm::Pred(place, fr) => Perm::Pred(f(place), fr),
        }
    }

    pub fn old<S: ToString + Clone>(self, label: S) -> Self {
        self.map_place(|p| p.old(label.clone()))
    }

    pub fn multiply_frac(&mut self, frac: Frac) {
        match self {
            Perm::Acc(_, ref mut fr) |
            Perm::Pred(_, ref mut fr) => *fr = *fr * frac,
        }
    }

    pub fn has_proper_prefix(&self, other: &vir::Place) -> bool {
        self.get_place().has_proper_prefix(other)
    }

    pub fn has_prefix(&self, other: &vir::Place) -> bool {
        self.get_place().has_prefix(other)
    }
}

impl<'a> Mul<&'a Frac> for Perm {
    type Output = Perm;

    fn mul(self, other: &Frac) -> Perm {
        self * (*other)
    }
}

impl Mul<Frac> for Perm {
    type Output = Perm;

    fn mul(self, other: Frac) -> Perm {
        match self {
            Perm::Acc(place, frac) => Perm::Acc(place, frac * other),
            Perm::Pred(place, frac) => Perm::Pred(place, frac * other),
        }
    }
}

impl fmt::Display for Perm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Perm::Acc(ref place, frac) => write!(f, "Acc({}, {})", place, frac),
            &Perm::Pred(ref place, frac) => write!(f, "Pred({}, {})", place, frac),
        }
    }
}

impl fmt::Debug for Perm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Perm::Acc(ref place, frac) => write!(f, "Acc({:?}, {})", place, frac),
            &Perm::Pred(ref place, frac) => write!(f, "Pred({:?}, {})", place, frac),
        }
    }
}


/// A set of permissions
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PermSet {
    acc_perms: HashMap<vir::Place, Frac>,
    pred_perms: HashMap<vir::Place, Frac>,
}

impl PermSet {
    pub fn empty() -> Self {
        PermSet {
            acc_perms: HashMap::new(),
            pred_perms: HashMap::new()
        }
    }

    /// Corresponds to an `inhale`
    /// Note: the amount of the permission is actually ignored
    pub fn add(&mut self, perm: Perm) {
        match perm {
            Perm::Acc(place, frac) => self.acc_perms.insert(place, frac),
            Perm::Pred(place, frac) => self.pred_perms.insert(place, frac),
        };
    }

    pub fn add_all(&mut self, mut perms: Vec<Perm>) {
        for perm in perms.drain(..) {
            self.add(perm);
        }
    }

    /// Corresponds to an `exhale`
    /// Note: the amount of the permission is actually ignored
    pub fn remove(&mut self, perm: &Perm) {
        match perm {
            Perm::Acc(..) => self.acc_perms.remove(perm.get_place()),
            Perm::Pred(..) => self.pred_perms.remove(perm.get_place()),
        };
    }

    pub fn remove_all(&mut self, mut perms: Vec<&Perm>) {
        for perm in perms.drain(..) {
            self.remove(perm);
        }
    }

    /// Corresponds to an `assert`
    /// Note: the amount of the permission is actually ignored
    pub fn contains(&self, perm: &Perm) -> bool {
        match perm {
            Perm::Acc(..) => self.acc_perms.contains_key(perm.get_place()),
            Perm::Pred(..) => self.pred_perms.contains_key(perm.get_place()),
        }
    }

    pub fn contains_all(&self, perms: Vec<&Perm>) -> bool {
        perms.iter().all(|x| self.contains(x))
    }

    pub fn perms(mut self) -> Vec<Perm> {
        let mut perms = vec![];
        for (place, frac) in self.acc_perms.drain() {
            perms.push(Perm::acc(place, frac));
        }
        for (place, frac) in self.pred_perms.drain() {
            perms.push(Perm::pred(place, frac));
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

impl<T> PermIterator for T where T: Iterator<Item = Perm> {
    fn collect_curr(&mut self) -> Vec<Perm> {
        self.filter(|perm| perm.is_curr()).collect()
    }

    fn group_by_label(&mut self) -> HashMap<Option<String>, Vec<Perm>> {
        let mut res_perms = HashMap::new();
        for perm in self {
            res_perms.entry(perm.get_label().cloned()).or_insert(vec![]).push(perm.clone());
        }
        res_perms
    }
}

pub fn place_frac_difference(mut left: HashMap<vir::Place, Frac>, mut right: HashMap<vir::Place, Frac>) -> HashMap<vir::Place, Frac> {
    for (place, right_frac) in right.drain() {
        match left.get(&place) {
            Some(left_frac) => {
                if *left_frac <= right_frac {
                    left.remove(&place);
                } else {
                    left.insert(place, *left_frac - right_frac);
                }
            },
            None => {}
        }
    }
    left
}

/// Set difference that takes into account that removing `x.f` also removes any `x.f.g.h`
pub fn perm_difference(mut left: HashSet<Perm>, mut right: HashSet<Perm>) -> HashSet<Perm> {
    let left_acc = left.iter().filter(|x| x.is_acc()).cloned();
    let left_pred = left.iter().filter(|x| x.is_pred()).cloned();
    let right_acc = right.iter().filter(|x| x.is_acc()).cloned();
    let right_pred = right.iter().filter(|x| x.is_pred()).cloned();
    let mut res = vec![];
    res.extend(
        place_frac_difference(
            left_acc.map(|p| (p.get_place().clone(), p.get_frac())).collect(),
            right_acc.map(|p| (p.get_place().clone(), p.get_frac())).collect(),
        ).drain().map(|(p, f)| Perm::Acc(p, f)).collect::<Vec<_>>()
    );
    res.extend(
        place_frac_difference(
            left_pred.map(|p| (p.get_place().clone(), p.get_frac())).collect(),
            right_pred.map(|p| (p.get_place().clone(), p.get_frac())).collect(),
        ).drain().map(|(p, f)| Perm::Pred(p, f)).collect::<Vec<_>>()
    );
    res.into_iter().collect()
}
