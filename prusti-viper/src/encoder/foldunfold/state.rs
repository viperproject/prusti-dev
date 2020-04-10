// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::vir;
use encoder::vir::ExprIterator;
use encoder::vir::PermAmount;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// paths on which we (may) have a full access permission
    acc: HashMap<vir::Expr, PermAmount>,
    /// paths on which we (may) have a full predicate permission
    pred: HashMap<vir::Expr, PermAmount>,
    quant: HashSet<vir::QuantifiedResourceAccess>,
    /// paths that have been "moved out" (for sure)
    moved: HashSet<vir::Expr>,
    /// Permissions currently framed
    framing_stack: Vec<PermSet>,
    /// Permissions that should be removed from the state
    /// This is a hack for restoring borrows
    dropped: HashSet<Perm>,
}

// See `get_all_quantified_predicate_instances` for
// the meaning of the three following structs
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedPredicateInstances {
    pub fully_instantiated: Vec<FullPredicateInstance>,
    pub partially_instantiated: Vec<PartialPredicateInstance>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FullPredicateInstance {
    pub instantiated_pred: vir::PredicateAccessPredicate,
    pub instantiated_from: vir::QuantifiedResourceAccess,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PartialPredicateInstance {
    pub partially_instantiated_quant: vir::QuantifiedResourceAccess,
    pub instantiated_from: vir::QuantifiedResourceAccess,
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
            quant: HashSet::new(),
            moved,
            framing_stack: vec![],
            dropped: HashSet::new(),
        }
    }

    // Skip consistency checks in release mode
    #[cfg(not(debug_assertions))]
    pub fn check_consistency(&self) {
        // Nothing
    }

    #[cfg(debug_assertions)]
    pub fn check_consistency(&self) {
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
                    && place.has_proper_prefix(&other_place)
                {
                    if !((self.pred[place] == PermAmount::Read ||
                          self.pred[place] == PermAmount::Remaining)
                        && self.pred[other_place] == PermAmount::Read)
                    {
                        panic!(
                            "Consistency error: state has pred {} ({}), but also pred {} ({})",
                            place, self.pred[place], other_place, self.pred[other_place]
                        );
                    }
                }
            }
        }
        for acc_place in self.acc.keys() {
            for pred_place in self.pred.keys() {
                if acc_place.is_simple_place()
                    && pred_place.is_simple_place()
                    && acc_place.has_proper_prefix(&pred_place)
                {
                    panic!(
                        "Consistency error: state has acc {}, but also pred {}",
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

    pub fn quantified(&self) -> &HashSet<vir::QuantifiedResourceAccess> {
        &self.quant
    }

    pub fn contains_acc(&self, place: &vir::Expr) -> bool {
        self.acc.contains_key(&place)
    }

    pub fn contains_pred(&self, place: &vir::Expr) -> bool {
        self.pred.contains_key(&place)
    }

    pub fn get_quantified(
        &self,
        quant: &vir::QuantifiedResourceAccess,
        check_perms: bool
    ) -> Option<&vir::QuantifiedResourceAccess> {
        self.quant.iter().find(|x| x.is_similar_to(quant, check_perms))
    }

    /// Get all quantified resources that can be instantiated for the given permission
    /// (as well as their instantiations)
    pub fn get_all_quantified_instances(&self, perm: &Perm) -> Vec<vir::InstantiationResult> {
        use encoder::vir::PlainResourceAccess::*;
        use std::cmp::Ordering::*;
        assert!(!perm.is_quantified(), "Nested quantified permissions are unsupported");
        let mut instances = self.quant
            .iter()
            // If we want a field access, then it's ok to either instantiate
            // against a quant. field access or a quant. predicate access
            // (because we can unfold the pred)
            // However, if we want a pred access, then we want to only instantiate
            // against a quant. pred.
            .filter(|quant| perm.is_acc() || (perm.is_pred() && quant.resource.is_pred()))
            .filter_map(|quant| quant.try_instantiate(perm.get_place()))
            .filter(|inst| inst.is_fully_instantiated())
            .collect::<Vec<_>>();

        instances.sort_unstable_by(|a, b| {
            let a_depth = a.instantiated().resource.get_place().place_depth();
            let b_depth = b.instantiated().resource.get_place().place_depth();
            if a_depth != b_depth {
                a_depth.cmp(&b_depth)
            } else {
                match (&a.instantiated().resource, &b.instantiated().resource) {
                    (Field(_), Field(_)) | (Predicate(_), Predicate(_)) => Equal,
                    (Field(_), Predicate(_)) => Less,
                    (Predicate(_), Field(_)) => Greater,
                }
            }
        });
        instances
    }

    /// Get all predicate instances that perfectly match the given place.
    /// We split the results in two groups: predicates that are fully instantiated
    /// (i.e., no forall vars remaining) and the ones that still contains free vars.
    pub fn get_all_quantified_predicate_instances(
        &self,
        pred_place: &vir::Expr
    )-> QuantifiedPredicateInstances {
        let (preds, quants): (Vec<_>, Vec<_>) = self.quantified()
            .iter()
            .filter(|quant| quant.resource.is_pred())
            .filter_map(move |quant|
                quant.try_instantiate(pred_place).map(|inst| (inst, quant.clone()))
            )
            .filter(|(inst, _)| inst.is_match_perfect())
            .partition(|(inst, _)| inst.is_fully_instantiated());

        let fully_instantiated = preds.into_iter()
            .map(|(inst, instantiated_from)| match inst.into_instantiated().resource {
                vir::PlainResourceAccess::Predicate(instantiated_pred) =>
                    FullPredicateInstance {
                        instantiated_pred,
                        instantiated_from
                    },
                _ => unreachable!()
            }).collect();

        let partially_instantiated = quants.into_iter()
            .map(|(inst, instantiated_from)| {
                let partially_instantiated_quant = inst.into_instantiated();
                PartialPredicateInstance {
                    partially_instantiated_quant,
                    instantiated_from
                }
            }).collect();

        QuantifiedPredicateInstances {
            fully_instantiated,
            partially_instantiated
        }
    }

    /// Get all quantified resources for which `perm_prefix_place` is a prefix.
    /// For instance, if we have `_1.val_ref` for `perm_prefix_place` and that
    /// we have the following quantified resources:
    /// `forall i :: (...) ==> acc(_1.val_ref.val_array[i].val_ref)`
    /// `forall i :: (...) ==> acc(isize(_1.val_ref.val_array[i].val_ref))`
    /// `forall i :: (...) ==> acc(_2.val_ref.val_array[i].val_ref)`
    /// Then this function will return the first two quantified resources.
    pub fn get_quantified_resources_suffixes_of(
        &self,
        perm_prefix_place: &vir::Expr
    ) -> Vec<vir::QuantifiedResourceAccess> {
        trace!("get_quantified_resources_suffixes_of: {}", perm_prefix_place);
        trace!("{}", self.display_quant());
        self.quant.iter()
            .filter(|quant| quant.resource.get_place().has_prefix(perm_prefix_place))
            .cloned()
            .collect()
    }

    pub fn contains_quantified(&self, quant: &vir::QuantifiedResourceAccess) -> bool {
        self.get_quantified(quant, false).is_some()
    }

    /// Note: the permission amount is currently ignored
    pub fn contains_perm(&self, item: &Perm) -> bool {
        match item {
            &Perm::Acc(ref place, _) => self.contains_acc(place),
            &Perm::Pred(ref place, _) => self.contains_pred(place),
            &Perm::Quantified(ref cond_perm) => self.contains_quantified(cond_perm)
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
        self.remove_quant_matching(|x| pred(x));
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

    pub fn remove_quant_matching<P>(&mut self, pred: P)
    where
        P: Fn(&vir::Expr) -> bool,
    {
        self.quant.retain(|e| !pred(e.resource.get_place()));
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

    pub fn display_quant(&self) -> String {
        let mut info = self
            .quant
            .iter()
            .map(|p| format!("  {}", p))
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

    pub fn insert_acc(&mut self, place: vir::Expr, perm: PermAmount) {
        trace!("insert_acc {}, {}", place, perm);
        if self.acc.contains_key(&place) {
            let new_perm = self.acc[&place] + perm;
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
    }

    pub fn insert_all_acc<I>(&mut self, items: I)
    where
        I: Iterator<Item = (vir::Expr, PermAmount)>,
    {
        for (place, perm) in items {
            self.insert_acc(place, perm);
        }
    }

    pub fn insert_pred(&mut self, place: vir::Expr, perm: PermAmount) {
        trace!("insert_pred {}, {}", place, perm);
        if self.pred.contains_key(&place) {
            let new_perm = self.pred[&place] + perm;
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
    }

    pub fn is_pred_an_instance(&self, place: &vir::Expr) -> bool {
        trace!("is_pred_an_instance {}", place);
        trace!("quant {}", self.display_quant());
        let res = self.quant.iter().any(|quant|
            quant.resource.is_pred() &&
                quant.try_instantiate(place)
                    .map(|res| res.is_match_perfect())
                    .unwrap_or(false)
        );
        trace!("is_pred_an_instance {} : {}", place, res);
        res
    }

    pub fn is_acc_an_instance(&self, place: &vir::Expr) -> bool {
        trace!("is_acc_an_instance {}", place);
        trace!("quant {}", self.display_quant());
        let res = self.quant.iter().any(|quant|
            quant.resource.is_field_acc() &&
                quant.try_instantiate(place)
                    .map(|res| res.is_match_perfect())
                    .unwrap_or(false)
        );
        trace!("is_acc_an_instance {} : {}", place, res);
        res
    }

    pub fn insert_quant(&mut self, quant: vir::QuantifiedResourceAccess) {
        trace!("insert_quant {}", quant);
        trace!("Quant state before: {{\n{}\n}}", self.display_quant());
        if let Some(curr_quant) = self.get_quantified(&quant, false).cloned() {
            let new_perm = curr_quant.get_perm_amount() + quant.get_perm_amount();
            assert!(
                new_perm == PermAmount::Write || new_perm == PermAmount::Read,
                "Trying to inhale {} predicate permission, while there is already {}",
                quant.get_perm_amount(),
                curr_quant.get_perm_amount()
            );
            self.quant.remove(&curr_quant);
            self.quant.insert(curr_quant.update_perm_amount(new_perm));
        } else {
            self.quant.insert(quant);
        }
        trace!("Quant state after: {{\n{}\n}}", self.display_quant());
    }

    pub fn insert_all_pred<I>(&mut self, items: I)
    where
        I: Iterator<Item = (vir::Expr, PermAmount)>,
    {
        for (place, perm) in items {
            self.insert_pred(place, perm);
        }
    }

    pub fn insert_all_quant<I>(&mut self, items: I)
    where
        I: Iterator<Item = vir::QuantifiedResourceAccess>,
    {
        for quant in items {
            self.insert_quant(quant);
        }
    }

    pub fn insert_moved(&mut self, place: vir::Expr) {
        //assert!(!self.pred.contains(&place), "Place {} is already in state (pred), so it can not be added.", place);
        self.moved.insert(place);
    }

    pub fn is_dropped(&self, item: &Perm) -> bool {
        self.dropped.contains(item)
    }

    pub fn insert_perm(&mut self, item: Perm) {
        match item {
            Perm::Acc(place, perm) => self.insert_acc(place, perm),
            Perm::Pred(place, perm) => self.insert_pred(place, perm),
            Perm::Quantified(cond) => self.insert_quant(cond),
        };
    }

    pub fn insert_all_perms<I>(&mut self, items: I)
    where
        I: Iterator<Item = Perm>,
    {
        for item in items {
            self.insert_perm(item);
        }
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

    pub fn remove_acc(&mut self, place: &vir::Expr, perm: PermAmount) {
        assert!(
            self.acc.contains_key(place),
            "Place {} is not in state (acc), so it can not be removed.",
            place
        );
        if self.acc[place] == perm {
            self.acc.remove(place);
        } else {
            self.acc.insert(place.clone(), self.acc[place] - perm);
        }
    }

    pub fn remove_pred(&mut self, place: &vir::Expr, perm: PermAmount) {
        trace!("remove_pred {}, {}", place, perm);
        assert!(
            self.pred.contains_key(place),
            "Place {} is not in state (pred), so it can not be removed.",
            place
        );
        if self.pred[place] == perm {
            self.pred.remove(place);
        } else {
            self.pred.insert(place.clone(), self.pred[place] - perm);
        }
    }

    pub fn remove_quant(&mut self, quant: &vir::QuantifiedResourceAccess) {
        trace!("remove_quant {}", quant);
        trace!("Quant state before: {{\n{}\n}}", self.display_quant());

        let curr_quant_entry = self.quant.iter().find(|x| x.is_similar_to(quant, false))
            .unwrap_or_else(||
                panic!("Quantified resource access {} not in state, \
                        so it can not be removed", quant)
            ).clone(); // The clone is unfortunate, but we can't self.quant.take(curr_quant_entry)
                       // because self.quant is already borrowed
        // Remove the current quant. entry, and add it back if some permission is remaining
        self.quant.remove(&curr_quant_entry);
        if curr_quant_entry.get_perm_amount() != quant.get_perm_amount() {
            let new_perm_amount = curr_quant_entry.get_perm_amount() - quant.get_perm_amount();
            self.quant.insert(curr_quant_entry.update_perm_amount(new_perm_amount));
        }

        trace!("Quant state after: {{\n{}\n}}", self.display_quant());
    }

    pub fn remove_perm(&mut self, item: &Perm) {
        match item {
            &Perm::Acc(_, perm) => self.remove_acc(item.get_place(), perm),
            &Perm::Pred(_, perm) => self.remove_pred(item.get_place(), perm),
            Perm::Quantified(quant) => self.remove_quant(quant),
        };
    }

    pub fn remove_all_perms<'a, I>(&mut self, items: I)
    where
        I: Iterator<Item = &'a Perm>,
    {
        for item in items {
            self.remove_perm(item);
        }
    }

    /// Restores the provided permission. It could be that the dropped
    /// permission is already in the state, for example, if the variable
    /// was assigned again as `x` in the following example:
    ///
    /// ```rust
    /// // pub fn test2(cond1: bool, mut a: ListNode) {
    /// //     let mut x = &mut a;
    /// //     if cond1 {
    /// //         x = match x.next {
    /// //             Some(box ref mut node) => node,
    /// //             None => x,
    /// //         };
    /// //     } // a.value is dropped during the merge.
    /// //     x.value.g.f = 4;
    /// // }
    /// ```
    /// In such a case, the function keeps the most generic variant of
    /// permissions.
    pub fn restore_dropped_perm(&mut self, item: Perm) {
        trace!("[enter] restore_dropped_perm item={}", item);
        for moved_place in &self.moved {
            trace!("  moved_place={}", moved_place);
        }
        match item {
            Perm::Acc(place, perm) => {
                self.remove_moved_matching(|p| place.has_prefix(p));
                self.restore_acc(place, perm);
            }
            Perm::Pred(place, perm) => {
                self.remove_moved_matching(|p| place.has_prefix(p));
                self.restore_pred(place, perm);
            }
            _ => unimplemented!(),
        };
        trace!("[exit] restore_dropped_perm");
    }

    fn restore_acc(&mut self, acc_place: vir::Expr, mut perm: PermAmount) {
        trace!("restore_acc {}, {}", acc_place, perm);
        if let Some(curr_perm_amount) = self.acc.get(&acc_place) {
            perm = perm + *curr_perm_amount;
        }
        if acc_place.is_simple_place() {
            for pred_place in self.pred.keys() {
                if pred_place.is_simple_place() && acc_place.has_proper_prefix(&pred_place) {
                    trace!(
                        "restore_acc {}: ignored (predicate already exists: {})",
                        acc_place,
                        pred_place
                    );
                    return;
                }
            }
        }
        self.acc.insert(acc_place, perm);
    }

    fn restore_pred(&mut self, pred_place: vir::Expr, mut perm: PermAmount) {
        trace!("restore_pred {}, {}", pred_place, perm);
        if let Some(curr_perm_amount) = self.pred.get(&pred_place) {
            perm = perm + *curr_perm_amount;
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
    }

    pub fn restore_dropped_perms<I>(&mut self, items: I)
    where
        I: Iterator<Item = Perm>,
    {
        trace!("[enter] restore_dropped_perms");
        for item in items {
            self.restore_dropped_perm(item);
        }
        self.check_consistency();
        trace!("[exit] restore_dropped_perms");
    }

    pub fn as_vir_expr(&self) -> vir::Expr {
        let mut exprs: Vec<vir::Expr> = vec![];
        for (place, perm) in self.acc.iter() {
            if !place.is_local() && place.is_curr() {
                if !self.is_dropped(&Perm::acc(place.clone(), *perm)) {
                    exprs.push(vir::Expr::acc_permission(place.clone(), *perm));
                }
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
                self.acc.remove(&place);
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

    pub fn end_frame(&mut self) {
        trace!("end_frame");
        trace!(
            "Before: {} frames are on the stack",
            self.framing_stack.len()
        );
        let framed_perms = self.framing_stack.pop().unwrap();
        debug!("Framed permissions: {}", framed_perms);
        for perm in framed_perms.perms().drain(..) {
            self.insert_perm(perm);
        }

        trace!(
            "After: {} frames are on the stack",
            self.framing_stack.len()
        );
    }
}

impl fmt::Display for State {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "acc: {{")?;
        writeln!(f, "{}", self.display_acc())?;
        writeln!(f, "}}")?;
        writeln!(f, "pred: {{")?;
        writeln!(f, "{}", self.display_pred())?;
        writeln!(f, "}}")?;
        writeln!(f, "quant: {{")?;
        writeln!(f, "{}", self.display_quant())?;
        writeln!(f, "}}")
    }
}
