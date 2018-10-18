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

/// A permission in the current state or in the (old) state of a label
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum LabelledPerm {
    Old(String, Perm),
    Curr(Perm)
}

impl LabelledPerm {
    pub fn acc_from_labelled_place(place: vir::LabelledPlace, frac: vir::Frac) -> Self {
        LabelledPerm::new(place.get_label(), Perm::Acc(place.get_place().clone(), frac))
    }

    pub fn pred_from_labelled_place(place: vir::LabelledPlace, frac: vir::Frac) -> Self {
        LabelledPerm::new(place.get_label(), Perm::Pred(place.get_place().clone(), frac))
    }

    pub fn new(opt_label: Option<&String>, perm: Perm) -> Self {
        match opt_label {
            Some(label) => LabelledPerm::old(label, perm),
            None => LabelledPerm::curr(perm),
        }
    }

    pub fn old(label: &str, perm: Perm) -> Self {
        LabelledPerm::Old(
            label.to_string(),
            perm
        )
    }

    pub fn curr(perm: Perm) -> Self {
        LabelledPerm::Curr(perm)
    }

    pub fn inner(&self) -> &Perm {
        self.get_perm()
    }

    pub fn unpack(self) -> (Option<String>, Perm) {
        match self {
            LabelledPerm::Old(label, perm) => (Some(label), perm),
            LabelledPerm::Curr(perm) => (None, perm),
        }
    }

    pub fn is_curr(&self) -> bool {
        match self {
            LabelledPerm::Curr(..) => true,
            _ => false
        }
    }

    pub fn is_old(&self) -> bool {
        match self {
            LabelledPerm::Old(..) => true,
            _ => false
        }
    }

    pub fn is_pred(&self) -> bool {
        self.get_perm().is_pred()
    }

    pub fn is_acc(&self) -> bool {
        self.get_perm().is_acc()
    }

    pub fn is_base(&self) -> bool {
        self.get_place().is_base()
    }

    pub fn get_perm(&self) -> &Perm {
        match self {
            LabelledPerm::Old(_, ref perm) |
            LabelledPerm::Curr( ref perm) => perm
        }
    }

    pub fn get_label(&self) -> Option<String> {
        match self {
            LabelledPerm::Old(ref label, _) => Some(label.clone()),
            LabelledPerm::Curr(_) => None,
        }
    }

    pub fn get_place(&self) -> vir::Place {
        self.get_perm().get_place()
    }

    pub fn get_type(&self) -> vir::Type {
        self.get_place().get_type().clone()
    }

    pub fn get_frac(&self) -> Frac {
        self.get_perm().get_frac()
    }

    pub fn get_labelled_place(&self) -> vir::LabelledPlace {
        match self {
            LabelledPerm::Old(label, perm) => vir::LabelledPlace::old(self.get_place(), label.to_string()),
            LabelledPerm::Curr(perm) => vir::LabelledPlace::curr(self.get_place()),
        }
    }

    pub fn get_labelled_place_and_frac(&self) -> (vir::LabelledPlace, Frac) {
        (self.get_labelled_place(), self.get_frac())
    }

    pub fn has_proper_prefix(&self, other: &vir::LabelledPlace) -> bool {
        self.get_labelled_place().has_proper_prefix(other)
    }

    pub fn has_prefix(&self, other: &vir::LabelledPlace) -> bool {
        self.get_labelled_place().has_prefix(other)
    }

    pub fn map_perm<F>(self, f: F) -> Self
        where F: Fn(Perm) -> Perm
    {
        match self {
            LabelledPerm::Old(label, perm) => LabelledPerm::Old(label, f(perm)),
            LabelledPerm::Curr(perm) => LabelledPerm::Curr(f(perm))
        }
    }

    pub fn map_place<F>(self, f: F) -> Self
        where F: Fn(vir::Place) -> vir::Place
    {
        self.map_perm(|p| p.map_place(|x| f(x)))
    }

    pub fn map_curr_place<F>(self, f: F) -> Self
        where F: Fn(vir::Place) -> vir::Place
    {
        if self.is_curr() {
            self.map_perm(|p| p.map_place(|x| f(x)))
        } else {
            self
        }
    }
}

impl<'a> Mul<&'a Frac> for LabelledPerm {
    type Output = LabelledPerm;

    fn mul(self, other: &Frac) -> LabelledPerm {
        self * (*other)
    }
}

impl Mul<Frac> for LabelledPerm {
    type Output = LabelledPerm;

    fn mul(self, other: Frac) -> LabelledPerm {
        match self {
            LabelledPerm::Old(label, perm) => LabelledPerm::Old(label, perm * other),
            LabelledPerm::Curr(perm) => LabelledPerm::Curr(perm * other),
        }
    }
}

impl fmt::Display for LabelledPerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.get_perm() {
            &Perm::Acc(ref place, frac) => write!(f, "Acc({}, {})", self.get_labelled_place(), frac),
            &Perm::Pred(ref place, frac) => write!(f, "Pred({}, {})", self.get_labelled_place(), frac),
        }
    }
}

impl fmt::Debug for LabelledPerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.get_perm() {
            &Perm::Acc(ref place, frac) => write!(f, "Acc({:?}, {})", self.get_labelled_place(), frac),
            &Perm::Pred(ref place, frac) => write!(f, "Pred({:?}, {})", self.get_labelled_place(), frac),
        }
    }
}

/// An access or predicate permission to a place
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Perm {
    Acc(vir::Place, Frac),
    Pred(vir::Place, Frac)
}

impl Perm {
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

    pub fn get_pred(&self) -> Option<&vir::Place> {
        match self {
            Perm::Pred(ref place, _) => Some(place),
            _ => None,
        }
    }

    pub fn get_frac(&self) -> Frac {
        match self {
            Perm::Acc(_, f) => *f,
            Perm::Pred(_, f) => *f,
        }
    }

    pub fn get_place(&self) -> vir::Place {
        match self {
            &Perm::Acc(ref place, _) |
            &Perm::Pred(ref place, _) => place.clone(),
        }
    }

    pub fn place_as_ref(&self) -> &vir::Place {
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

    pub fn multiply_frac(&mut self, frac: Frac) {
        match self {
            Perm::Acc(_, ref mut fr) |
            Perm::Pred(_, ref mut fr) => *fr = *fr * frac,
        }
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
pub struct LabelledPermSet {
    acc_perms: HashMap<vir::LabelledPlace, Frac>,
    pred_perms: HashMap<vir::LabelledPlace, Frac>,
}

impl LabelledPermSet {
    pub fn empty() -> Self {
        LabelledPermSet {
            acc_perms: HashMap::new(),
            pred_perms: HashMap::new()
        }
    }

    /// Corresponds to an `inhale`
    /// Note: the amount of the permission is actually ignored
    pub fn add(&mut self, perm: LabelledPerm) {
        match perm.unpack() {
            (label, Perm::Acc(place, frac)) => self.acc_perms.insert(vir::LabelledPlace::new(place, label), frac),
            (label, Perm::Pred(place, frac)) => self.pred_perms.insert(vir::LabelledPlace::new(place, label), frac),
        };
    }

    pub fn add_all(&mut self, mut perms: Vec<LabelledPerm>) {
        for perm in perms.drain(..) {
            self.add(perm);
        }
    }

    /// Corresponds to an `exhale`
    /// Note: the amount of the permission is actually ignored
    pub fn remove(&mut self, perm: &LabelledPerm) {
        match perm.get_perm() {
            Perm::Acc(..) => self.acc_perms.remove(&perm.get_labelled_place()),
            Perm::Pred(..) => self.pred_perms.remove(&perm.get_labelled_place()),
        };
    }

    pub fn remove_all(&mut self, mut perms: Vec<&LabelledPerm>) {
        for perm in perms.drain(..) {
            self.remove(perm);
        }
    }

    /// Corresponds to an `assert`
    /// Note: the amount of the permission is actually ignored
    pub fn contains(&self, perm: &LabelledPerm) -> bool {
        match perm.get_perm() {
            Perm::Acc(..) => self.acc_perms.contains_key(&perm.get_labelled_place()),
            Perm::Pred(..) => self.pred_perms.contains_key(&perm.get_labelled_place()),
        }
    }

    pub fn contains_all(&self, perms: Vec<&LabelledPerm>) -> bool {
        perms.iter().all(|x| self.contains(x))
    }

    pub fn perms(mut self) -> Vec<LabelledPerm> {
        let mut perms = vec![];
        for (labelled_place, frac) in self.acc_perms.drain() {
            let place = labelled_place.get_place().clone();
            let label = labelled_place.get_label();
            perms.push(LabelledPerm::new(label, Perm::Acc(place, frac)))
        }
        for (labelled_place, frac) in self.pred_perms.drain() {
            let place = labelled_place.get_place().clone();
            let label = labelled_place.get_label();
            perms.push(LabelledPerm::new(label, Perm::Pred(place, frac)))
        }
        perms
    }
}

impl fmt::Display for LabelledPermSet {
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


pub trait LabelledPermIterator {
    fn collect_curr(&mut self) -> Vec<Perm>;
    fn group_by_label(&mut self) -> HashMap<Option<String>, Vec<LabelledPerm>>;
}

impl<T> LabelledPermIterator for T where T: Iterator<Item = LabelledPerm> {
    fn collect_curr(&mut self) -> Vec<Perm> {
        self.flat_map(|mop| match mop {
            LabelledPerm::Curr(p) => Some(p),
            _ => None
        }).collect()
    }

    fn group_by_label(&mut self) -> HashMap<Option<String>, Vec<LabelledPerm>> {
        let mut perms = HashMap::new();
        for x in self {
            perms.entry(x.get_label()).or_insert(vec![]).push(x.clone());
        }
        perms
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

pub fn perm_difference(mut left: HashSet<Perm>, mut right: HashSet<Perm>) -> HashSet<Perm> {
    let left_acc = left.iter().filter(|x| x.is_acc()).cloned();
    let left_pred = left.iter().filter(|x| x.is_pred()).cloned();
    let right_acc = right.iter().filter(|x| x.is_acc()).cloned();
    let right_pred = right.iter().filter(|x| x.is_pred()).cloned();
    let mut res = vec![];
    res.extend(
        place_frac_difference(
            left_acc.map(|p| (p.get_place(), p.get_frac())).collect(),
            right_acc.map(|p| (p.get_place(), p.get_frac())).collect(),
        ).drain().map(|(p, f)| Perm::Acc(p, f)).collect::<Vec<_>>()
    );
    res.extend(
        place_frac_difference(
            left_pred.map(|p| (p.get_place(), p.get_frac())).collect(),
            right_pred.map(|p| (p.get_place(), p.get_frac())).collect(),
        ).drain().map(|(p, f)| Perm::Pred(p, f)).collect::<Vec<_>>()
    );
    res.into_iter().collect()
}

/// Takes into account that removing `x.f` also removes any `x.f.g.h`
pub fn labelled_perm_difference(mut left: HashSet<LabelledPerm>, mut right: HashSet<LabelledPerm>) -> HashSet<LabelledPerm> {
    let mut res = vec![];
    let mut left_curr = HashSet::new();
    for item in left.drain() {
        match item {
            LabelledPerm::Old(..) => {
                res.push(item);
            }
            LabelledPerm::Curr(perm) => {
                left_curr.insert(perm);
            }
        }
    }
    let right_curr: HashSet<_> = right.drain().flat_map(|item| match item {
        LabelledPerm::Old(..) => None,
        LabelledPerm::Curr(perm) => Some(perm),
    }).collect();
    res.extend(
        perm_difference(left_curr, right_curr).into_iter()
            .map(|x| LabelledPerm::Curr(x))
            .collect::<Vec<_>>()
    );
    res.into_iter().collect()
}
