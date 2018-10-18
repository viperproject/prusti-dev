// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::vir;
use encoder::vir::Frac;
use encoder::vir::{Zero, One};
use encoder::vir::ExprIterator;
use std::collections::HashSet;
use std::collections::HashMap;
use std::iter::FromIterator;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// paths on which we (may) have a full access permission
    acc: HashMap<vir::LabelledPlace, Frac>,
    /// paths on which we (may) have a full predicate permission
    pred: HashMap<vir::LabelledPlace, Frac>,
    /// paths that have been "moved out" (for sure)
    moved: HashSet<vir::Place>,
    /// Permissions currently framed
    framing_stack: Vec<LabelledPermSet>,
}

impl State {
    pub fn new(acc: HashMap<vir::LabelledPlace, Frac>, pred: HashMap<vir::LabelledPlace, Frac>, moved: HashSet<vir::Place>) -> Self {
        State {
            acc,
            pred,
            moved,
            framing_stack: vec![]
        }
    }

    pub fn check_consistency(&self) {
        // Check access permissions
        for place in self.pred.keys() {
            if place.is_curr() && !self.contains_acc(place) {
                panic!(
                    "Consistency error: state has pred {}, but not acc {}",
                    place,
                    place
                );
            }
        }
        for place in self.acc.keys() {
            if !place.get_place().is_base() {
                if !self.contains_acc(&place.clone().map_place(|p| p.parent().unwrap().clone())) {
                    panic!(
                        "Consistency error: state has acc {}, but not acc {}",
                        place,
                        place.clone().map_place(|p| p.parent().unwrap().clone())
                    );
                }
            }
        }
        // Check predicates and moved paths
        for place in self.pred.keys() {
            for other_place in self.pred.keys() {
                if place.get_place().has_proper_prefix(&other_place.get_place()) {
                    panic!(
                        "Consistency error: state has pred {}, but also pred {}",
                        place,
                        other_place
                    );
                }
            }
        }
        for acc_place in self.acc.keys() {
            for pred_place in self.pred.keys() {
                if acc_place.get_place().has_proper_prefix(&pred_place.get_place()) {
                    panic!(
                        "Consistency error: state has acc {}, but also pred {}",
                        acc_place,
                        pred_place
                    );
                }
            }
        }
        for acc_place in self.acc.keys() {
            for moved_place in &self.moved {
                if acc_place.get_place().has_proper_prefix(moved_place) {
                    panic!(
                        "Consistency error: state has acc {}, but also moved path {}",
                        acc_place,
                        moved_place
                    );
                }
            }
        }
        for pred_place in self.pred.keys() {
            for moved_place in &self.moved {
                if pred_place.get_place().has_prefix(moved_place) {
                    panic!(
                        "Consistency error: state has pred {}, but also moved path {}",
                        pred_place,
                        moved_place
                    );
                }
                if moved_place.has_prefix(pred_place.get_place()) && pred_place.is_curr() {
                    panic!(
                        "Consistency error: state has pred {}, but also moved path {}",
                        pred_place,
                        moved_place
                    );
                }
            }
        }
        // Check moved
        for place in &self.moved {
            if !self.contains_acc(&vir::LabelledPlace::curr(place.clone())) &&
                !self.framing_stack.iter().any(|fs|
                    fs.contains(&LabelledPerm::curr(Perm::Acc(place.clone(), Frac::one())))
                ) {
                panic!(
                    "Consistency error: state has moved path {}, but not acc {} (not even a framed one)",
                    place,
                    place
                );
            }
        }
    }

    pub fn replace_local_vars<F>(&mut self, replace: F) where F: Fn(&vir::LocalVar) -> vir::LocalVar {
        for coll in vec![&mut self.acc, &mut self.pred] {
            let new_values = coll.clone().into_iter()
                .map(|(p, frac)| {
                    (p.map_place(|place| {
                        let base_var = place.base();
                        let new_base_var = replace(base_var);
                        let new_place = place.clone().replace_prefix(&vir::Place::Base(base_var.clone()), new_base_var.into());
                        new_place
                    }), frac)
                });
            coll.clear();
            for (key, value) in new_values {
                coll.insert(key, value);
            }
        }

        for coll in vec![&mut self.moved] {
            let new_values = coll.clone().into_iter().map(
                |place| {
                    let base_var = place.base();
                    let new_base_var = replace(base_var);
                    place.clone().replace_prefix(&vir::Place::Base(base_var.clone()), new_base_var.into())
                }
            );
            coll.clear();
            for item in new_values {
                coll.insert(item);
            }
        }
    }


    pub fn replace_labels<F>(&mut self, replace: F) where F: Fn(Option<String>) -> Option<String> {
        for coll in vec![&mut self.acc, &mut self.pred] {
            let new_values = coll.clone().into_iter()
                .map(|(p, frac)| {
                    (p.map_label(|l| replace(l)), frac)
                });
            coll.clear();
            for (key, value) in new_values {
                coll.insert(key, value);
            }
        }
    }

    pub fn acc(&self) -> &HashMap<vir::LabelledPlace, Frac> {
        &self.acc
    }

    pub fn acc_places(&self) -> HashSet<vir::LabelledPlace> {
        self.acc.keys().cloned().collect()
    }

    pub fn acc_leafes(&self) -> HashSet<vir::LabelledPlace> {
        let mut acc_leafes = HashSet::new();
        for place in self.acc.keys() {
            if !self.is_proper_prefix_of_some_acc(place) {
                acc_leafes.insert(place.clone());
            }
        }
        acc_leafes
    }

    pub fn pred(&self) -> &HashMap<vir::LabelledPlace, Frac> {
        &self.pred
    }

    pub fn pred_places(&self) -> HashSet<vir::LabelledPlace> {
        self.pred.keys().cloned().collect()
    }

    pub fn moved(&self) -> &HashSet<vir::Place> {
        &self.moved
    }

    pub fn framing_stack(&self) -> &Vec<LabelledPermSet> {
        &self.framing_stack
    }

    pub fn set_acc(&mut self, acc: HashMap<vir::LabelledPlace, Frac>) {
        self.acc = acc
    }

    pub fn set_pred(&mut self, pred: HashMap<vir::LabelledPlace, Frac>) {
        self.pred = pred
    }

    pub fn set_moved(&mut self, moved: HashSet<vir::Place>) {
        self.moved = moved
    }

    pub fn contains_acc(&self, place: &vir::LabelledPlace) -> bool {
        self.acc.contains_key(&place)
    }

    pub fn contains_pred(&self, place: &vir::LabelledPlace) -> bool {
        self.pred.contains_key(&place)
    }

    pub fn contains_moved(&self, place: &vir::Place) -> bool {
        self.moved.contains(&place)
    }

    /// Note: the fraction is currently ignored
    pub fn contains_perm(&self, item: &LabelledPerm) -> bool {
        match item.get_perm() {
            &Perm::Acc(ref place, _) => self.contains_acc(&item.get_labelled_place()),
            &Perm::Pred(ref place, _) => self.contains_pred(&item.get_labelled_place()),
        }
    }

    pub fn contains_all_perms<'a, I>(&mut self, mut items: I) -> bool where I: Iterator<Item = &'a LabelledPerm> {
        items.all(|x| self.contains_perm(x))
    }

    pub fn is_proper_prefix_of_some_acc(&self, prefix: &vir::LabelledPlace) -> bool {
        for place in self.acc.keys() {
            if place.has_proper_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_proper_prefix_of_some_pred(&self, prefix: &vir::LabelledPlace) -> bool {
        for place in self.pred.keys() {
            if place.has_proper_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_proper_prefix_of_some_moved(&self, prefix: &vir::Place) -> bool {
        for place in &self.moved {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_prefix_of_some_acc(&self, prefix: &vir::LabelledPlace) -> bool {
        for place in self.acc.keys() {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_prefix_of_some_pred(&self, prefix: &vir::LabelledPlace) -> bool {
        for place in self.pred.keys() {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_prefix_of_some_moved(&self, prefix: &vir::Place) -> bool {
        for place in &self.moved {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn intersect_acc(&mut self, acc_set: &HashSet<vir::LabelledPlace>) {
        let mut new_acc = HashMap::new();
        for (place, frac) in self.acc.drain() {
            if acc_set.contains(&place) {
                new_acc.insert(place, frac);
            }
        }
        self.acc = new_acc;
    }

    pub fn intersect_pred(&mut self, pred_set: &HashSet<vir::LabelledPlace>) {
        let mut new_pred = HashMap::new();
        for (place, frac) in self.pred.drain() {
            if pred_set.contains(&place) {
                new_pred.insert(place, frac);
            }
        }
        self.pred = new_pred;
    }

    pub fn intersect_moved(&mut self, other_moved: &HashSet<vir::Place>) {
        self.moved = HashSet::from_iter(self.moved.intersection(other_moved).cloned());
    }

    pub fn remove_all(&mut self) {
        self.remove_matching_place(|_| true);
    }

    pub fn remove_matching_place<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.remove_acc_matching_place(|x| pred(x));
        self.remove_pred_matching_place(|x| pred(x));
        self.remove_moved_matching(|x| pred(x));
    }

    pub fn remove_acc_matching_place<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.acc.retain(|e, _| !pred(e.get_place()));
    }

    pub fn remove_pred_matching_place<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.pred.retain(|e, _| !pred(e.get_place()));
    }

    pub fn remove_acc_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::LabelledPlace) -> bool
    {
        self.acc.retain(|e, _| !pred(e));
    }

    pub fn remove_pred_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::LabelledPlace) -> bool
    {
        self.pred.retain(|e, _| !pred(e));
    }

    pub fn remove_moved_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.moved.retain(|e| !pred(e));
    }

    pub fn display_acc(&self) -> String {
        self.acc.iter().map(|(p, f)| format!("{}: {}", p, f)).collect::<Vec<String>>().join(", ")
    }

    pub fn display_pred(&self) -> String {
        self.pred.iter().map(|(p, f)| format!("{}: {}", p, f)).collect::<Vec<String>>().join(", ")
    }

    pub fn display_moved(&self) -> String {
        self.moved.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
    }

    pub fn display_debug_acc(&self) -> String {
        self.acc.iter().map(|(place, frac)| format!("({:?}, {})", place, frac)).collect::<Vec<String>>().join(", ")
    }

    pub fn display_debug_pred(&self) -> String {
        self.pred.iter().map(|(place, frac)| format!("({:?}, {})", place, frac)).collect::<Vec<String>>().join(", ")
    }

    pub fn display_debug_moved(&self) -> String {
        self.moved.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
    }

    pub fn insert_acc(&mut self, place: vir::LabelledPlace, frac: Frac) {
        trace!("insert_acc {}, {}", place, frac);
        if self.acc.contains_key(&place) {
            let new_frac = self.acc[&place] + frac;
            assert!(new_frac <= Frac::one(), "insert_acc: {} <= 1", new_frac);
            self.acc.insert(place, new_frac);
        } else {
            self.acc.insert(place, frac);
        }
    }

    pub fn insert_all_acc<I>(&mut self, items: I) where I: Iterator<Item = (vir::LabelledPlace, Frac)> {
        for (place, frac) in items {
            self.insert_acc(place, frac);
        }
    }

    pub fn insert_pred(&mut self, place: vir::LabelledPlace, frac: Frac) {
        trace!("insert_pred {}, {}", place, frac);
        if self.pred.contains_key(&place) {
            let new_frac = self.pred[&place] + frac;
            assert!(new_frac <= Frac::one(), "{} <= 1", new_frac);
            self.pred.insert(place, new_frac);
        } else {
            self.pred.insert(place, frac);
        }
    }

    pub fn insert_all_pred<I>(&mut self, items: I) where I: Iterator<Item = (vir::LabelledPlace, Frac)> {
        for (place, frac) in items {
            self.insert_pred(place, frac);
        }
    }

    pub fn insert_moved(&mut self, place: vir::Place) {
        //assert!(!self.pred.contains(&place), "Place {} is already in state (pred), so it can not be added.", place);
        self.moved.insert(place);
    }

    pub fn insert_all_moved<I>(&mut self, items: I) where I: Iterator<Item = vir::Place> {
        for item in items {
            self.insert_moved(item);
        }
    }

    pub fn insert_perm(&mut self, item: LabelledPerm) {
        match item.get_perm() {
            &Perm::Acc(_, frac) => self.insert_acc(item.get_labelled_place(), frac),
            &Perm::Pred(_, frac) => self.insert_pred(item.get_labelled_place(), frac),
        };
    }

    pub fn insert_all_perms<I>(&mut self, items: I) where I: Iterator<Item=LabelledPerm> {
        for item in items {
            self.insert_perm(item);
        }
    }

    pub fn remove_acc_place(&mut self, place: &vir::LabelledPlace) -> Frac {
        assert!(self.acc.contains_key(place), "Place {} is not in state (acc), so it can not be removed.", place);
        self.acc.remove(place).unwrap()
    }

    pub fn remove_pred_place(&mut self, place: &vir::LabelledPlace) -> Frac {
        assert!(self.pred.contains_key(place), "Place {} is not in state (pred), so it can not be removed.", place);
        self.pred.remove(place).unwrap()
    }

    pub fn remove_acc(&mut self, place: &vir::LabelledPlace, frac: Frac) {
        assert!(self.acc.contains_key(place), "Place {} is not in state (acc), so it can not be removed.", place);
        assert!(self.acc[place] >= frac);
        if self.acc[place] == frac {
            self.acc.remove(place);
        } else {
            self.acc.insert(place.clone(), self.acc[place] - frac);
        }
    }

    pub fn remove_pred(&mut self, place: &vir::LabelledPlace, frac: Frac) {
        trace!("remove_pred {}, {}", place, frac);
        assert!(self.pred.contains_key(place), "Place {} is not in state (pred), so it can not be removed.", place);
        assert!(self.pred[place] >= frac, "{} >= {}", frac, self.pred[place]);
        if self.pred[place] == frac {
            self.pred.remove(place);
        } else {
            self.pred.insert(place.clone(), self.pred[place] - frac);
        }
    }

    pub fn remove_moved(&mut self, place: &vir::Place) {
        assert!(self.moved.contains(place), "Place {} is not in state (moved), so it can not be removed.", place);
        self.moved.remove(place);
    }

    pub fn remove_perm(&mut self, item: &LabelledPerm) {
        match item.get_perm() {
            &Perm::Acc(_, frac) => self.remove_acc(&item.get_labelled_place(), frac),
            &Perm::Pred(_, frac) => self.remove_pred(&item.get_labelled_place(), frac)
        };
    }

    pub fn remove_all_perms<'a, I>(&mut self, items: I) where I: Iterator<Item = &'a LabelledPerm> {
        for item in items {
            self.remove_perm(item);
        }
    }

    pub fn as_vir_expr(&self) -> vir::Expr {
        let mut exprs: Vec<vir::Expr> = vec![];
        for (place, frac) in self.acc.iter() {
            if !place.get_place().is_base() {
                exprs.push(
                    vir::Expr::acc_permission(place.clone(), *frac)
                );
            }
        }
        for (place, frac) in self.pred.iter() {
            if let Some(perm) = vir::Expr::pred_permission(place.clone(), *frac) {
                exprs.push(perm);
            }
        }
        exprs.into_iter().conjoin()
    }

    pub fn begin_frame(&mut self) {
        trace!("begin_frame");
        trace!("Before: {} frames are on the stack", self.framing_stack.len());
        let mut framed_perms = LabelledPermSet::empty();
        for (place, frac) in self.acc.clone().into_iter() {
            if !place.get_place().is_base() {
                self.acc.remove(&place);
                framed_perms.add(LabelledPerm::new(place.get_label(), Perm::Acc(place.get_place().clone(), frac)));
            }
        }
        for (place, frac) in self.pred.drain() {
            framed_perms.add(LabelledPerm::new(place.get_label(), Perm::Pred(place.get_place().clone(), frac)));
        }
        debug!("Framed permissions: {}", framed_perms);
        self.framing_stack.push(framed_perms);
        trace!("After: {} frames are on the stack", self.framing_stack.len());
    }

    pub fn end_frame(&mut self) {
        trace!("end_frame");
        trace!("Before: {} frames are on the stack", self.framing_stack.len());
        let mut framed_perms = self.framing_stack.pop().unwrap();
        debug!("Framed permissions: {}", framed_perms);
        for perm in framed_perms.perms().drain(..) {
            self.insert_perm(perm);
        }

        trace!("After: {} frames are on the stack", self.framing_stack.len());
    }

    pub fn get_available_frac(&self, perm: &LabelledPerm) -> Frac {
        match perm.get_perm() {
            Perm::Acc(..) => self.acc.get(&perm.get_labelled_place()).cloned().unwrap_or(Frac::zero()),
            Perm::Pred(..) => self.pred.get(&perm.get_labelled_place()).cloned().unwrap_or(Frac::zero()),
        }
    }
}
