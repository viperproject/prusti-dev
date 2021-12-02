// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::foldunfold::{perm::*, FoldUnfoldError};
use log::{debug, trace};
use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    fmt,
    ops::{Add, Sub},
};
use vir_crate::polymorphic::{self as vir, ExprIterator, PermAmount};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// paths on which we (may) have a full access permission
    acc: HashMap<vir::Expr, PermAmount>,
    /// paths on which we (may) have a full predicate permission
    pred: HashMap<vir::Expr, PermAmount>,
    /// paths that have been "moved out" (for sure)
    moved: HashSet<vir::Expr>,
    /// Permissions currently framed
    framing_stack: Vec<PermSet>,
    /// Permissions that should be removed from the state
    /// This is a hack for restoring borrows
    dropped: HashSet<Perm>,
}

impl State {
    pub fn new(
        acc: HashMap<vir::Expr, PermAmount>,
        pred: HashMap<vir::Expr, PermAmount>,
        moved: HashSet<vir::Expr>,
    ) -> Self {
        State {
            acc,
            pred,
            moved,
            framing_stack: vec![],
            dropped: HashSet::new(),
        }
    }

    pub fn check_consistency(&self) {
        // Skip consistency checks in release mode
        if cfg!(not(debug_assertions)) {
            return;
        }

        // Check access permissions
        for place in self.pred.keys() {
            if place.is_simple_place() && !self.contains_acc(place) {
                let contains_parent_pred = if let Some(parent) = place.get_parent() {
                    self.pred.contains_key(&parent)
                } else {
                    false
                };
                if !contains_parent_pred
                    && self.pred[place] != PermAmount::Remaining
                    && self.pred[place] != PermAmount::Read
                    && !place.is_mir_reference()
                {
                    trace!("place: {:?}", place);
                    trace!("Acc state: {{\n{}\n}}", self.display_acc());
                    trace!("Pred state: {{\n{}\n}}", self.display_pred());
                    panic!(
                        "Consistency error: state has pred {}, but not acc {}",
                        place, place
                    );
                }
            }
        }
        for place in self.acc.keys() {
            if place.is_simple_place() && !place.is_local() {
                let parent = place.clone().get_parent().unwrap();
                if !self.contains_acc(&parent) {
                    if self.acc[place] == PermAmount::Read {
                        let grand_parent = parent.clone().get_parent().unwrap();
                        if grand_parent.is_local() {
                            continue;
                        }
                    }
                    panic!(
                        "Consistency error: state has acc {}, but not acc {}",
                        place,
                        place.get_parent().unwrap()
                    );
                }
            }
        }
        // Check predicates and moved paths
        for place in self.pred.keys() {
            for other_place in self.pred.keys() {
                if place.is_simple_place()
                    && other_place.is_simple_place()
                    && place.has_proper_prefix(other_place)
                    && !((self.pred[place] == PermAmount::Read
                        || self.pred[place] == PermAmount::Remaining)
                        && self.pred[other_place] == PermAmount::Read)
                {
                    panic!(
                        "Consistency error: state has pred {} ({}), but also pred {} ({})",
                        place, self.pred[place], other_place, self.pred[other_place]
                    );
                }
            }
        }
        for acc_place in self.acc.keys() {
            for pred_place in self.pred.keys() {
                if acc_place.is_simple_place()
                    && pred_place.is_simple_place()
                    && acc_place.has_proper_prefix(pred_place)
                    && matches!(self.pred[pred_place], PermAmount::Write)
                {
                    panic!(
                        "Consistency error: state has acc {}, but also a full pred {}",
                        acc_place, pred_place
                    );
                }
            }
        }
        for acc_place in self.acc.keys() {
            for moved_place in &self.moved {
                if moved_place.is_simple_place()
                    && acc_place.is_simple_place()
                    && acc_place.has_proper_prefix(moved_place)
                {
                    panic!(
                        "Consistency error: state has acc {}, but also moved path {}",
                        acc_place, moved_place
                    );
                }
            }
        }
        for pred_place in self.pred.keys() {
            for moved_place in &self.moved {
                if moved_place.is_simple_place()
                    && pred_place.is_simple_place()
                    && pred_place.has_prefix(moved_place)
                {
                    panic!(
                        "Consistency error: state has pred {}, but also moved path {}",
                        pred_place, moved_place
                    );
                }
                if moved_place.is_simple_place()
                    && pred_place.is_simple_place()
                    && moved_place.has_prefix(pred_place)
                {
                    panic!(
                        "Consistency error: state has pred {}, but also moved path {}",
                        pred_place, moved_place
                    );
                }
            }
        }
        //      // Check moved
        //      TODO: Replace moved with initialisation information.
        //      for place in &self.moved {
        //          if place.is_simple_place() && !self.contains_acc(place) &&
        //              !place.is_mir_reference() &&
        //              !self.framing_stack.iter().any(|fs|
        //                  fs.contains(&Perm::Acc(place.clone(), PermAmount::Write))
        //              ) {
        //              panic!(
        //                  "Consistency error: state has moved path {}, but not acc {} (not even a framed one)",
        //                  place,
        //                  place
        //              );
        //          }
        //      }
    }

    pub fn replace_places<F>(&mut self, replace: F)
    where
        F: Fn(vir::Expr) -> vir::Expr,
    {
        for coll in vec![&mut self.acc, &mut self.pred] {
            let new_values = coll
                .clone()
                .into_iter()
                .map(|(place, perm)| (replace(place), perm));
            coll.clear();
            for (key, value) in new_values {
                coll.insert(key, value);
            }
        }
    }

    pub fn acc(&self) -> &HashMap<vir::Expr, PermAmount> {
        &self.acc
    }

    pub fn acc_places(&self) -> HashSet<vir::Expr> {
        self.acc.keys().cloned().collect()
    }

    pub fn acc_leaves(&self) -> HashSet<vir::Expr> {
        let mut acc_leaves = HashSet::new();
        for place in self.acc.keys() {
            if !self.is_proper_prefix_of_some_acc(place) {
                acc_leaves.insert(place.clone());
            }
        }
        acc_leaves
    }

    pub fn pred(&self) -> &HashMap<vir::Expr, PermAmount> {
        &self.pred
    }

    pub fn pred_places(&self) -> HashSet<vir::Expr> {
        self.pred.keys().cloned().collect()
    }

    pub fn moved(&self) -> &HashSet<vir::Expr> {
        &self.moved
    }

    pub fn set_moved(&mut self, moved: HashSet<vir::Expr>) {
        self.moved = moved
    }

    pub fn contains_acc(&self, place: &vir::Expr) -> bool {
        self.acc.contains_key(place)
    }

    pub fn contains_pred(&self, place: &vir::Expr) -> bool {
        self.pred.contains_key(place)
    }

    /// Note: the permission amount is currently ignored
    pub fn contains_perm(&self, item: &Perm) -> bool {
        match item {
            Perm::Acc(ref _place, _) => self.contains_acc(item.get_place()),
            Perm::Pred(ref _place, _) => self.contains_pred(item.get_place()),
        }
    }

    pub fn contains_all_perms<'a, I>(&mut self, mut items: I) -> bool
    where
        I: Iterator<Item = &'a Perm>,
    {
        items.all(|x| self.contains_perm(x))
    }

    pub fn is_proper_prefix_of_some_acc(&self, prefix: &vir::Expr) -> bool {
        for place in self.acc.keys() {
            if place.has_proper_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_prefix_of_some_acc(&self, prefix: &vir::Expr) -> bool {
        for place in self.acc.keys() {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_prefix_of_some_pred(&self, prefix: &vir::Expr) -> bool {
        for place in self.pred.keys() {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn is_prefix_of_some_moved(&self, prefix: &vir::Expr) -> bool {
        for place in &self.moved {
            if place.has_prefix(prefix) {
                return true;
            }
        }
        false
    }

    pub fn remove_all(&mut self) {
        self.remove_matching_place(|_| true);
    }

    pub fn remove_matching_place<P>(&mut self, pred: P)
    where
        P: Fn(&vir::Expr) -> bool,
    {
        self.remove_acc_matching(|x| pred(x));
        self.remove_pred_matching(|x| pred(x));
        self.remove_moved_matching(|x| pred(x));
    }

    pub fn remove_acc_matching<P>(&mut self, pred: P)
    where
        P: Fn(&vir::Expr) -> bool,
    {
        self.acc.retain(|e, _| !pred(e));
    }

    pub fn remove_pred_matching<P>(&mut self, pred: P)
    where
        P: Fn(&vir::Expr) -> bool,
    {
        self.pred.retain(|e, _| !pred(e));
    }

    pub fn remove_moved_matching<P>(&mut self, pred: P)
    where
        P: Fn(&vir::Expr) -> bool,
    {
        self.moved.retain(|e| !pred(e));
    }

    pub fn display_acc(&self) -> String {
        let mut info = self
            .acc
            .iter()
            .map(|(p, f)| format!("  {}: {}", p, f))
            .collect::<Vec<String>>();
        info.sort();
        info.join(",\n")
    }

    pub fn display_pred(&self) -> String {
        let mut info = self
            .pred
            .iter()
            .map(|(p, f)| format!("  {}: {}", p, f))
            .collect::<Vec<String>>();
        info.sort();
        info.join(",\n")
    }

    pub fn display_moved(&self) -> String {
        let mut info = self
            .moved
            .iter()
            .map(|x| format!("  {}", x))
            .collect::<Vec<String>>();
        info.sort();
        info.join(",\n")
    }

    pub fn insert_acc(
        &mut self,
        place: vir::Expr,
        perm: PermAmount,
    ) -> Result<(), FoldUnfoldError> {
        trace!("insert_acc {}, {}", place, perm);
        if self.acc.contains_key(&place) {
            let new_perm = self.acc[&place].add(perm)?;
            assert!(
                new_perm == PermAmount::Write || new_perm == PermAmount::Read,
                "Trying to inhale {} access permission, while there is already {}",
                perm,
                self.acc[&place]
            );
            self.acc.insert(place, new_perm);
        } else {
            self.acc.insert(place, perm);
        }
        Ok(())
    }

    pub fn insert_all_acc<I>(&mut self, items: I) -> Result<(), FoldUnfoldError>
    where
        I: Iterator<Item = (vir::Expr, PermAmount)>,
    {
        for (place, perm) in items {
            self.insert_acc(place, perm)?;
        }
        Ok(())
    }

    pub fn insert_pred(
        &mut self,
        place: vir::Expr,
        perm: PermAmount,
    ) -> Result<(), FoldUnfoldError> {
        trace!("insert_pred {}, {}", place, perm);
        if self.pred.contains_key(&place) {
            let new_perm = self.pred[&place].add(perm)?;
            assert!(
                new_perm == PermAmount::Write || new_perm == PermAmount::Read,
                "Trying to inhale {} predicate permission, while there is already {}",
                perm,
                self.pred[&place]
            );
            self.pred.insert(place, new_perm);
        } else {
            self.pred.insert(place, perm);
        }
        Ok(())
    }

    pub fn insert_all_pred<I>(&mut self, items: I) -> Result<(), FoldUnfoldError>
    where
        I: Iterator<Item = (vir::Expr, PermAmount)>,
    {
        for (place, perm) in items {
            self.insert_pred(place, perm)?;
        }
        Ok(())
    }

    pub fn insert_moved(&mut self, place: vir::Expr) {
        //assert!(!self.pred.contains(&place), "Place {} is already in state (pred), so it can not be added.", place);
        self.moved.insert(place);
    }

    pub fn is_dropped(&self, item: &Perm) -> bool {
        self.dropped.contains(item)
    }

    pub fn insert_perm(&mut self, item: Perm) -> Result<(), FoldUnfoldError> {
        match item {
            Perm::Acc(place, perm) => self.insert_acc(place, perm),
            Perm::Pred(place, perm) => self.insert_pred(place, perm),
        }
    }

    pub fn insert_all_perms<I>(&mut self, items: I) -> Result<(), FoldUnfoldError>
    where
        I: Iterator<Item = Perm>,
    {
        for item in items {
            self.insert_perm(item)?;
        }
        Ok(())
    }

    pub fn remove_acc_place(&mut self, place: &vir::Expr) -> PermAmount {
        assert!(
            self.acc.contains_key(place),
            "Place {} is not in state (acc), so it can not be removed.",
            place
        );
        self.acc.remove(place).unwrap()
    }

    pub fn remove_pred_place(&mut self, place: &vir::Expr) -> PermAmount {
        assert!(
            self.pred.contains_key(place),
            "Place {} is not in state (pred), so it can not be removed.",
            place
        );
        self.pred.remove(place).unwrap()
    }

    pub fn remove_acc(
        &mut self,
        place: &vir::Expr,
        perm: PermAmount,
    ) -> Result<(), FoldUnfoldError> {
        assert!(
            self.acc.contains_key(place),
            "Place {} is not in state (acc), so it can not be removed.",
            place
        );
        if self.acc[place] == perm {
            self.acc.remove(place);
        } else {
            self.acc.insert(place.clone(), self.acc[place].sub(perm)?);
        }
        Ok(())
    }

    pub fn remove_pred(
        &mut self,
        place: &vir::Expr,
        perm: PermAmount,
    ) -> Result<(), FoldUnfoldError> {
        trace!("remove_pred {}, {}", place, perm);
        if !self.pred.contains_key(place) {
            return Err(FoldUnfoldError::FailedToRemovePred(place.clone(), perm));
        }
        if self.pred[place] == perm {
            self.pred.remove(place).unwrap();
        } else {
            self.pred.insert(place.clone(), self.pred[place].sub(perm)?);
        }
        Ok(())
    }

    pub fn remove_perm(&mut self, item: &Perm) -> Result<(), FoldUnfoldError> {
        match item {
            Perm::Acc(_, perm) => self.remove_acc(item.get_place(), *perm),
            Perm::Pred(_, perm) => self.remove_pred(item.get_place(), *perm),
        }
    }

    pub fn remove_all_perms<I, P>(&mut self, items: I) -> Result<(), FoldUnfoldError>
    where
        I: Iterator<Item = P>,
        P: Borrow<Perm>,
    {
        for item in items {
            self.remove_perm(item.borrow())?;
        }
        Ok(())
    }

    /// Restores the provided permission. It could be that the dropped
    /// permission is already in the state, for example, if the variable
    /// was assigned again as `x` in the following example:
    ///
    /// ```rust,ignore
    /// pub fn test2(cond1: bool, mut a: ListNode) {
    ///     let mut x = &mut a;
    ///     if cond1 {
    ///         x = match x.next {
    ///             Some(box ref mut node) => node,
    ///             None => x,
    ///         };
    ///     } // a.value is dropped during the merge.
    ///     x.value.g.f = 4;
    /// }
    /// ```
    /// In such a case, the function keeps the most generic variant of
    /// permissions.
    pub fn restore_dropped_perm(&mut self, item: Perm) -> Result<(), FoldUnfoldError> {
        trace!("[enter] restore_dropped_perm item={}", item);
        for moved_place in &self.moved {
            trace!("  moved_place={}", moved_place);
        }
        match item {
            Perm::Acc(place, perm) => {
                self.remove_moved_matching(|p| place.has_prefix(p));
                self.restore_acc(place, perm)?;
            }
            Perm::Pred(place, perm) => {
                self.remove_moved_matching(|p| place.has_prefix(p));
                self.restore_pred(place, perm)?;
            }
        };
        trace!("[exit] restore_dropped_perm");
        Ok(())
    }

    fn restore_acc(
        &mut self,
        acc_place: vir::Expr,
        mut perm: PermAmount,
    ) -> Result<(), FoldUnfoldError> {
        trace!("restore_acc {}, {}", acc_place, perm);
        if let Some(curr_perm_amount) = self.acc.get(&acc_place) {
            perm = perm.add(*curr_perm_amount)?;
        }
        if acc_place.is_simple_place() {
            for pred_place in self.pred.keys() {
                if pred_place.is_simple_place() && acc_place.has_proper_prefix(pred_place) {
                    trace!(
                        "restore_acc {}: ignored (predicate already exists: {})",
                        acc_place,
                        pred_place
                    );
                    return Ok(());
                }
            }
        }
        self.acc.insert(acc_place, perm);
        Ok(())
    }

    fn restore_pred(
        &mut self,
        pred_place: vir::Expr,
        mut perm: PermAmount,
    ) -> Result<(), FoldUnfoldError> {
        trace!("restore_pred {}, {}", pred_place, perm);
        if let Some(curr_perm_amount) = self.pred.get(&pred_place) {
            perm = perm.add(*curr_perm_amount)?;
            //trace!("restore_pred {}: ignored (state already contains place)", pred_place);
            //return;
        }
        if pred_place.is_simple_place() {
            self.acc.retain(|acc_place, _| {
                if acc_place.is_simple_place() && acc_place.has_proper_prefix(&pred_place) {
                    trace!(
                        "restore_pred {}: drop conflicting acc {}",
                        pred_place,
                        acc_place
                    );
                    false
                } else {
                    true
                }
            });
        }
        self.pred.insert(pred_place, perm);
        Ok(())
    }

    pub fn restore_dropped_perms<I>(&mut self, items: I) -> Result<(), FoldUnfoldError>
    where
        I: Iterator<Item = Perm>,
    {
        trace!("[enter] restore_dropped_perms");
        for item in items {
            self.restore_dropped_perm(item)?;
        }
        self.check_consistency();
        trace!("[exit] restore_dropped_perms");
        Ok(())
    }

    pub fn as_vir_expr(&self) -> vir::Expr {
        let mut exprs: Vec<vir::Expr> = vec![];
        for (place, perm) in self.acc.iter() {
            if !place.is_local()
                && place.is_curr()
                && !self.is_dropped(&Perm::acc(place.clone(), *perm))
            {
                exprs.push(vir::Expr::acc_permission(place.clone(), *perm));
            }
        }
        for (place, perm_amount) in self.pred.iter() {
            if let Some(perm) = vir::Expr::pred_permission(place.clone(), *perm_amount) {
                if !self.is_dropped(&Perm::pred(place.clone(), *perm_amount)) && place.is_curr() {
                    exprs.push(perm);
                }
            }
        }
        exprs.into_iter().conjoin()
    }

    pub fn begin_frame(&mut self) {
        trace!("begin_frame");
        trace!(
            "Before: {} frames are on the stack",
            self.framing_stack.len()
        );
        let mut framed_perms = PermSet::empty();
        for (place, perm) in self.acc.clone().into_iter() {
            if !place.is_local() {
                self.acc.remove(&place).unwrap();
                framed_perms.add(Perm::Acc(place.clone(), perm));
            }
        }
        for (place, perm) in self.pred.drain() {
            framed_perms.add(Perm::Pred(place.clone(), perm));
        }
        debug!("Framed permissions: {}", framed_perms);
        self.framing_stack.push(framed_perms);
        trace!(
            "After: {} frames are on the stack",
            self.framing_stack.len()
        );
    }

    pub fn end_frame(&mut self) -> Result<(), FoldUnfoldError> {
        trace!("end_frame");
        trace!(
            "Before: {} frames are on the stack",
            self.framing_stack.len()
        );
        let framed_perms = self.framing_stack.pop().unwrap();
        debug!("Framed permissions: {}", framed_perms);
        for perm in framed_perms.perms().drain(..) {
            self.insert_perm(perm)?;
        }

        trace!(
            "After: {} frames are on the stack",
            self.framing_stack.len()
        );
        Ok(())
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "acc: {{")?;
        writeln!(f, "{}", self.display_acc())?;
        writeln!(f, "}}")?;
        writeln!(f, "pred: {{")?;
        writeln!(f, "{}", self.display_pred())?;
        writeln!(f, "}}")
    }
}
