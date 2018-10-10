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
    acc: HashMap<vir::Place, Frac>,
    /// paths on which we (may) have a full predicate permission
    pred: HashMap<vir::Place, Frac>,
    /// paths that have been "moved out" (for sure)
    moved: HashSet<vir::Place>,
    /// paths that are blocked because they may have been mutably borrowed
    borrowed: HashSet<vir::Place>,
    /// Permissions currently framed
    framing_stack: Vec<PermSet>,
}

impl State {
    pub fn new(acc: HashMap<vir::Place, Frac>, pred: HashMap<vir::Place, Frac>, moved: HashSet<vir::Place>, borrowed: HashSet<vir::Place>) -> Self {
        State {
            acc,
            pred,
            moved,
            borrowed,
            framing_stack: vec![]
        }
    }

    pub fn check_consistency(&self) {
        // Check access permissions
        for place in self.pred.keys() {
            if !self.contains_acc(place) {
                panic!(
                    "Consistency error: state has pred {}, but not acc {}",
                    place,
                    place
                );
            }
        }
        for place in self.acc.keys() {
            if !place.is_base() {
                if !self.contains_acc(place.parent().unwrap()) {
                    panic!(
                        "Consistency error: state has acc {}, but not acc {}",
                        place,
                        place.parent().unwrap()
                    );
                }
            }
        }
        // Check predicates and moved paths
        for place in self.pred.keys() {
            for other_place in self.pred.keys() {
                if place.has_proper_prefix(other_place) {
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
                if acc_place.has_proper_prefix(pred_place) {
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
                if acc_place.has_proper_prefix(moved_place) {
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
                if pred_place.has_prefix(moved_place) {
                    panic!(
                        "Consistency error: state has pred {}, but also moved path {}",
                        pred_place,
                        moved_place
                    );
                }
                if moved_place.has_prefix(pred_place) {
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
            if !self.contains_acc(place) && !self.framing_stack.iter().any(|fs| fs.contains(&Perm::Acc(place.clone(), Frac::one()))) {
                panic!(
                    "Consistency error: state has moved path {}, but not acc {} (not even a framed one)",
                    place,
                    place
                );
            }
        }
        // Check borrowed
        for place in &self.borrowed {
            for other_place in &self.borrowed {
                if place.has_proper_prefix(other_place) {
                    panic!(
                        "Consistency error: state has borrowed {}, but also borrowed {}",
                        place,
                        other_place
                    );
                }
            }
        }
        for borrowed_place in &self.borrowed {
            if self.is_proper_prefix_of_some_acc(borrowed_place) {
                panic!(
                    "Consistency error: borrowed place {} can not be a proper prefix of some access permissions",
                    borrowed_place
                );
            }
            if self.is_prefix_of_some_pred(borrowed_place) {
                panic!(
                    "Consistency error: borrowed place {} can not be a prefix of some predicate permissions",
                    borrowed_place
                );
            }
            if self.is_prefix_of_some_moved(borrowed_place) {
                panic!(
                    "Consistency error: borrowed place {} can not be a prefix of some moved path",
                    borrowed_place
                );
            }
        }
    }

    pub fn replace_local_vars<F>(&mut self, replace: F) where F: Fn(&vir::LocalVar) -> vir::LocalVar {
        for coll in vec![&mut self.acc, &mut self.pred] {
            let new_values = coll.clone().into_iter().map(
                |(place, frac)| {
                    let base_var = place.base();
                    let new_base_var = replace(base_var);
                    let new_place = place.clone().replace_prefix(&vir::Place::Base(base_var.clone()), new_base_var.into());
                    (new_place , frac)
                }
            );
            coll.clear();
            for (key, value) in new_values {
                coll.insert(key, value);
            }
        }

        for coll in vec![&mut self.moved, &mut self.borrowed] {
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

    pub fn acc(&self) -> &HashMap<vir::Place, Frac> {
        &self.acc
    }

    pub fn acc_places(&self) -> HashSet<vir::Place> {
        self.acc.keys().cloned().collect()
    }

    pub fn acc_leafes(&self) -> HashSet<vir::Place> {
        let mut acc_leafes = HashSet::new();
        for place in self.acc.keys() {
            if !self.is_proper_prefix_of_some_acc(place) {
                acc_leafes.insert(place.clone());
            }
        }
        acc_leafes
    }

    pub fn pred(&self) -> &HashMap<vir::Place, Frac> {
        &self.pred
    }

    pub fn pred_places(&self) -> HashSet<vir::Place> {
        self.pred.keys().cloned().collect()
    }

    pub fn moved(&self) -> &HashSet<vir::Place> {
        &self.moved
    }

    pub fn borrowed(&self) -> &HashSet<vir::Place> {
        &self.borrowed
    }

    pub fn framing_stack(&self) -> &Vec<PermSet> {
        &self.framing_stack
    }

    pub fn set_acc(&mut self, acc: HashMap<vir::Place, Frac>) {
        self.acc = acc
    }

    pub fn set_pred(&mut self, pred: HashMap<vir::Place, Frac>) {
        self.pred = pred
    }

    pub fn set_moved(&mut self, moved: HashSet<vir::Place>) {
        self.moved = moved
    }

    pub fn set_borrowed(&mut self, borrowed: HashSet<vir::Place>) {
        self.borrowed = borrowed
    }

    pub fn contains_acc(&self, place: &vir::Place) -> bool {
        self.acc.contains_key(&place)
    }

    pub fn contains_pred(&self, place: &vir::Place) -> bool {
        self.pred.contains_key(&place)
    }

    pub fn contains_moved(&self, place: &vir::Place) -> bool {
        self.moved.contains(&place)
    }

    pub fn contains_borrowed(&self, place: &vir::Place) -> bool {
        self.borrowed.contains(&place)
    }

    /// Note: the fraction is currently ignored
    pub fn contains_perm(&self, item: &Perm) -> bool {
        match item {
            &Perm::Acc(ref place, _) => self.contains_acc(&place),
            &Perm::Pred(ref place, _) => self.contains_pred(&place),
        }
    }

    pub fn contains_all_perms<'a, I>(&mut self, mut items: I) -> bool where I: Iterator<Item = &'a Perm> {
        items.all(|x| self.contains_perm(x))
    }

    pub fn is_proper_prefix_of_some_acc(&self, prefix: &vir::Place) -> bool {
        for place in self.acc.keys() {
            if place.has_proper_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_proper_prefix_of_some_pred(&self, prefix: &vir::Place) -> bool {
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

    pub fn is_proper_prefix_of_some_borrowed(&self, prefix: &vir::Place) -> bool {
        for place in &self.borrowed {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_prefix_of_some_acc(&self, prefix: &vir::Place) -> bool {
        for place in self.acc.keys() {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_prefix_of_some_pred(&self, prefix: &vir::Place) -> bool {
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

    pub fn is_prefix_of_some_borrowed(&self, prefix: &vir::Place) -> bool {
        for place in &self.borrowed {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn intersect_acc(&mut self, acc_set: &HashSet<vir::Place>) {
        let mut new_acc = HashMap::new();
        for (place, frac) in self.acc.drain() {
            if acc_set.contains(&place) {
                new_acc.insert(place, frac);
            }
        }
        self.acc = new_acc;
    }

    pub fn intersect_pred(&mut self, pred_set: &HashSet<vir::Place>) {
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

    pub fn intersect_borrowed(&mut self, other_borrowed: &HashSet<vir::Place>) {
        self.borrowed = HashSet::from_iter(self.borrowed.intersection(other_borrowed).cloned());
    }

    pub fn remove_all(&mut self) {
        self.remove_matching(|_| true);
    }

    pub fn remove_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.remove_acc_matching_place(|x| pred(x));
        self.remove_pred_matching_place(|x| pred(x));
        self.remove_moved_matching(|x| pred(x));
        self.remove_borrowed_matching(|x| pred(x));
    }

    pub fn remove_acc_matching_place<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.acc.retain(|e, _| !pred(e));
    }

    pub fn remove_pred_matching_place<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.pred.retain(|e, _| !pred(e));
    }

    pub fn remove_moved_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.moved.retain(|e| !pred(e));
    }

    pub fn remove_borrowed_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.borrowed.retain(|e| !pred(e));
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

    pub fn display_borrowed(&self) -> String {
        self.borrowed.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
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

    pub fn display_debug_borrowed(&self) -> String {
        self.borrowed.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
    }

    pub fn insert_acc(&mut self, place: vir::Place, frac: Frac) {
        trace!("insert_acc {}, {}", place, frac);
        if self.acc.contains_key(&place) {
            let new_frac = self.acc[&place] + frac;
            assert!(new_frac <= Frac::one(), "{} <= 1", new_frac);
            self.acc.insert(place, new_frac);
        } else {
            self.acc.insert(place, frac);
        }
    }

    pub fn insert_all_acc<I>(&mut self, items: I) where I: Iterator<Item = (vir::Place, Frac)> {
        for (place, frac) in items {
            self.insert_acc(place, frac);
        }
    }

    pub fn insert_pred(&mut self, place: vir::Place, frac: Frac) {
        trace!("insert_pred {}, {}", place, frac);
        if self.pred.contains_key(&place) {
            let new_frac = self.pred[&place] + frac;
            assert!(new_frac <= Frac::one(), "{} <= 1", new_frac);
            self.pred.insert(place, new_frac);
        } else {
            self.pred.insert(place, frac);
        }
    }

    pub fn insert_all_pred<I>(&mut self, items: I) where I: Iterator<Item = (vir::Place, Frac)> {
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

    pub fn insert_borrowed(&mut self, place: vir::Place) {
        //assert!(!self.pred.contains(&place), "Place {} is already in state (pred), so it can not be added.", place);
        self.borrowed.insert(place);
    }

    pub fn insert_all_borrowed<I>(&mut self, items: I) where I: Iterator<Item = vir::Place> {
        for item in items {
            self.insert_borrowed(item);
        }
    }

    pub fn insert_perm(&mut self, item: Perm) {
        match item {
            Perm::Acc(place, frac) => self.insert_acc(place, frac),
            Perm::Pred(place, frac) => self.insert_pred(place, frac),
        };
    }

    pub fn insert_all_perms<I>(&mut self, items: I) where I: Iterator<Item =Perm> {
        for item in items {
            self.insert_perm(item);
        }
    }

    pub fn remove_acc_place(&mut self, place: &vir::Place) -> Frac {
        assert!(self.acc.contains_key(place), "Place {} is not in state (acc), so it can not be removed.", place);
        self.acc.remove(place).unwrap()
    }

    pub fn remove_pred_place(&mut self, place: &vir::Place) -> Frac {
        assert!(self.pred.contains_key(place), "Place {} is not in state (pred), so it can not be removed.", place);
        self.pred.remove(place).unwrap()
    }

    pub fn remove_acc(&mut self, place: &vir::Place, frac: Frac) {
        assert!(self.acc.contains_key(place), "Place {} is not in state (acc), so it can not be removed.", place);
        assert!(self.acc[place] >= frac);
        if self.acc[place] == frac {
            self.acc.remove(place);
        } else {
            self.acc.insert(place.clone(), self.acc[place] - frac);
        }
    }

    pub fn remove_pred(&mut self, place: &vir::Place, frac: Frac) {
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

    pub fn remove_borrowed(&mut self, place: &vir::Place) {
        assert!(self.borrowed.contains(place), "Place {} is not in state (borrowed), so it can not be removed.", place);
        self.borrowed.remove(place);
    }

    pub fn remove_perm(&mut self, item: &Perm) {
        match item {
            &Perm::Acc(ref place, frac) => self.remove_acc(place, frac),
            &Perm::Pred(ref place, frac) => self.remove_pred(place, frac)
        };
    }

    pub fn remove_all_perms<'a, I>(&mut self, items: I) where I: Iterator<Item = &'a Perm> {
        for item in items {
            self.remove_perm(item);
        }
    }

    pub fn as_vir_expr(&self) -> vir::Expr {
        let mut exprs: Vec<vir::Expr> = vec![];
        for (place, frac) in self.acc.iter() {
            if !place.is_base() {
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
        let mut framed_perms = PermSet::empty();
        for (place, frac) in self.acc.clone().into_iter() {
            if !place.is_base() {
                self.acc.remove(&place);
                framed_perms.add(Perm::Acc(place, frac));
            }
        }
        for (place, frac) in self.pred.drain() {
            framed_perms.add(Perm::Pred(place, frac))
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

    pub fn get_available_frac(&self, perm: &Perm) -> Frac {
        match perm {
            Perm::Acc(ref place, _) => self.acc.get(place).cloned().unwrap_or(Frac::zero()),
            Perm::Pred(ref place, _) => self.pred.get(place).cloned().unwrap_or(Frac::zero()),
        }
    }
}
