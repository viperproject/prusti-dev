// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::vir;
use encoder::vir::ExprIterator;
use std::collections::HashSet;
use std::iter::FromIterator;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// paths on which we (may) have a full access permission
    acc: HashSet<vir::Place>,
    /// paths on which we (may) have a full predicate permission
    pred: HashSet<vir::Place>,
    /// paths that have been "moved out" (for sure)
    moved: HashSet<vir::Place>,
    /// paths that are blocked because they may have been mutably borrowed
    borrowed: HashSet<vir::Place>,
}

impl State {
    pub fn new(acc: HashSet<vir::Place>, pred: HashSet<vir::Place>, moved: HashSet<vir::Place>, borrowed: HashSet<vir::Place>) -> Self {
        State {
            acc,
            pred,
            moved,
            borrowed,
        }
    }

    pub fn check_consistency(&self) {
        // Check access permissions
        for place in &self.pred {
            if !self.contains_acc(place) {
                panic!(
                    "Consistency error: state has pred {}, but not acc {}",
                    place,
                    place
                );
            }
        }
        for place in &self.moved {
            if !self.contains_acc(place) {
                panic!(
                    "Consistency error: state has moved path {}, but not acc {}",
                    place,
                    place
                );
            }
        }
        for place in &self.acc {
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
        for place in &self.pred {
            for other_place in &self.pred {
                if place.has_proper_prefix(other_place) {
                    panic!(
                        "Consistency error: state has pred {}, but also pred {}",
                        place,
                        other_place
                    );
                }
            }
        }
        for acc_place in &self.acc {
            for pred_place in &self.pred {
                if acc_place.has_proper_prefix(pred_place) {
                    panic!(
                        "Consistency error: state has acc {}, but also pred {}",
                        acc_place,
                        pred_place
                    );
                }
            }
        }
        for acc_place in &self.acc {
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
        for pred_place in &self.pred {
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
        let collections = vec![
            &mut self.acc,
            &mut self.pred,
            &mut self.moved,
            &mut self.borrowed,
        ];

        for coll in collections {
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

    pub fn acc(&self) -> &HashSet<vir::Place> {
        &self.acc
    }

    pub fn acc_leafes(&self) -> HashSet<vir::Place> {
        let mut acc_leafes = HashSet::new();
        for place in &self.acc {
            if !self.is_proper_prefix_of_some_acc(place) {
                acc_leafes.insert(place.clone());
            }
        }
        acc_leafes
    }

    pub fn pred(&self) -> &HashSet<vir::Place> {
        &self.pred
    }

    pub fn moved(&self) -> &HashSet<vir::Place> {
        &self.moved
    }

    pub fn borrowed(&self) -> &HashSet<vir::Place> {
        &self.borrowed
    }

    pub fn set_acc(&mut self, acc: HashSet<vir::Place>) {
        self.acc = acc
    }

    pub fn set_pred(&mut self, pred: HashSet<vir::Place>) {
        self.pred = pred
    }

    pub fn set_moved(&mut self, moved: HashSet<vir::Place>) {
        self.moved = moved
    }

    pub fn set_borrowed(&mut self, borrowed: HashSet<vir::Place>) {
        self.borrowed = borrowed
    }

    pub fn contains_acc(&self, place: &vir::Place) -> bool {
        self.acc.contains(&place)
    }

    pub fn contains_pred(&self, place: &vir::Place) -> bool {
        self.pred.contains(&place)
    }

    pub fn contains_moved(&self, place: &vir::Place) -> bool {
        self.moved.contains(&place)
    }

    pub fn contains_borrowed(&self, place: &vir::Place) -> bool {
        self.borrowed.contains(&place)
    }

    pub fn contains_perm(&self, item: &Perm) -> bool {
        match item {
            &Perm::Acc(ref place) => self.contains_acc(&place),
            &Perm::Pred(ref place) => self.contains_pred(&place),
        }
    }

    pub fn contains_all_perms<'a, I>(&mut self, mut items: I) -> bool where I: Iterator<Item = &'a Perm> {
        items.all(|x| self.contains_perm(x))
    }

    pub fn is_proper_prefix_of_some_acc(&self, prefix: &vir::Place) -> bool {
        for place in &self.acc {
            if place.has_proper_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn is_proper_prefix_of_some_pred(&self, prefix: &vir::Place) -> bool {
        for place in &self.pred {
            if place.has_proper_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn is_proper_prefix_of_some_moved(&self, prefix: &vir::Place) -> bool {
        for place in &self.moved {
            if place.has_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn is_proper_prefix_of_some_borrowed(&self, prefix: &vir::Place) -> bool {
        for place in &self.borrowed {
            if place.has_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn is_prefix_of_some_acc(&self, prefix: &vir::Place) -> bool {
        for place in &self.acc {
            if place.has_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn is_prefix_of_some_pred(&self, prefix: &vir::Place) -> bool {
        for place in &self.pred {
            if place.has_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn is_prefix_of_some_moved(&self, prefix: &vir::Place) -> bool {
        for place in &self.moved {
            if place.has_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn is_prefix_of_some_borrowed(&self, prefix: &vir::Place) -> bool {
        for place in &self.borrowed {
            if place.has_prefix(prefix) {
                return true
            }
        }
        return false
    }

    pub fn intersect_acc(&mut self, other_acc: &HashSet<vir::Place>) {
        self.acc = HashSet::from_iter(self.acc.intersection(other_acc).cloned());
    }

    pub fn intersect_pred(&mut self, other_pred: &HashSet<vir::Place>) {
        self.pred = HashSet::from_iter(self.pred.intersection(other_pred).cloned());
    }

    pub fn intersect_moved(&mut self, other_moved: &HashSet<vir::Place>) {
        self.moved = HashSet::from_iter(self.moved.intersection(other_moved).cloned());
    }

    pub fn intersect_borrowed(&mut self, other_borrowed: &HashSet<vir::Place>) {
        self.borrowed = HashSet::from_iter(self.borrowed.intersection(other_borrowed).cloned());
    }

    pub fn remove_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.remove_acc_matching(|x| pred(x));
        self.remove_pred_matching(|x| pred(x));
        self.remove_moved_matching(|x| pred(x));
        self.remove_borrowed_matching(|x| pred(x));
    }

    pub fn remove_acc_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.acc.retain(|e| !pred(e));
    }

    pub fn remove_pred_matching<P>(&mut self, pred: P)
        where P: Fn(&vir::Place) -> bool
    {
        self.pred.retain(|e| !pred(e));
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
        self.acc.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
    }

    pub fn display_pred(&self) -> String {
        self.pred.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
    }

    pub fn display_moved(&self) -> String {
        self.moved.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
    }

    pub fn display_borrowed(&self) -> String {
        self.borrowed.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
    }

    pub fn display_debug_acc(&self) -> String {
        self.acc.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
    }

    pub fn display_debug_pred(&self) -> String {
        self.pred.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
    }

    pub fn display_debug_moved(&self) -> String {
        self.moved.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
    }

    pub fn display_debug_borrowed(&self) -> String {
        self.borrowed.iter().map(|x| format!("{:?}", x)).collect::<Vec<String>>().join(", ")
    }

    pub fn insert_acc(&mut self, place: vir::Place) {
        //assert!(!self.acc.contains(&place), "Place {} is already in state (acc), so it can not be added.", place);
        self.acc.insert(place);
    }

    pub fn insert_all_acc<I>(&mut self, items: I) where I: Iterator<Item = vir::Place> {
        for item in items {
            self.insert_acc(item);
        }
    }

    pub fn insert_pred(&mut self, place: vir::Place) {
        //assert!(!self.pred.contains(&place), "Place {} is already in state (pred), so it can not be added.", place);
        self.pred.insert(place);
    }

    pub fn insert_all_pred<I>(&mut self, items: I) where I: Iterator<Item = vir::Place> {
        for item in items {
            self.insert_pred(item);
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
            Perm::Acc(place) => self.insert_acc(place),
            Perm::Pred(place) => self.insert_pred(place),
        };
    }

    pub fn insert_all_perms<I>(&mut self, items: I) where I: Iterator<Item =Perm> {
        for item in items {
            self.insert_perm(item);
        }
    }

    pub fn remove_acc(&mut self, place: &vir::Place) {
        assert!(self.acc.contains(place), "Place {} is not in state (acc), so it can not be removed.", place);
        self.acc.remove(place);
    }

    pub fn remove_pred(&mut self, place: &vir::Place) {
        assert!(self.pred.contains(place), "Place {} is not in state (pred), so it can not be removed.", place);
        self.pred.remove(place);
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
            &Perm::Acc(ref place) => self.remove_acc(place),
            &Perm::Pred(ref place) => self.remove_pred(place)
        }
    }

    pub fn remove_all_perms<'a, I>(&mut self, items: I) where I: Iterator<Item = &'a Perm> {
        for item in items {
            self.remove_perm(item);
        }
    }

    pub fn as_vir_expr(&self) -> vir::Expr {
        let mut exprs: Vec<vir::Expr> = vec![];
        for place in &self.acc {
            if !place.is_base() {
                exprs.push(
                    vir::Expr::acc_permission(place.clone(), vir::Perm::full())
                );
            }
        }
        for place in &self.pred {
            if let Some(perm) = vir::Expr::pred_permission(place.clone(), vir::Perm::full()) {
                exprs.push(perm);
            }
        }
        exprs.into_iter().conjoin()
    }
}
