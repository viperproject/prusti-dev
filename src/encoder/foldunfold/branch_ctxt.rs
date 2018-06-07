// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashSet;
use std::collections::HashMap;
use encoder::vir;
use std::iter::FromIterator;
use encoder::foldunfold::acc_or_pred::*;
use encoder::foldunfold::requirements::*;
use encoder::foldunfold::state::*;

const DEBUG_FOLDUNFOLD: bool = false;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchCtxt {
    state: State,
    /// The definition of the predicates
    predicates: HashMap<String, vir::Predicate>
}

/// Returns the elements of A1 or A2 that have a prefix in the other set.
///
/// e.g.
/// definitely_preserved(
///   { a, b.c, d.e.f, d.g },
///   { a, b.c.d, b.c.e, d.e,h }
/// ) = { a, b.c.d, b.c.e, d.e.f }
fn definitely_preserved(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    let mut res = HashSet::new();
    for left_item in left.iter() {
        for right_item in right.iter() {
            if right_item.has_prefix(left_item) {
                res.insert(right_item.clone());
            }
            if left_item.has_prefix(right_item) {
                res.insert(left_item.clone());
            }
        }
    }
    res
}

/// Returns the elements of A1 that are a prefix of at least one element in A2.
///
/// e.g.
/// filter_prefixes_of(
///   { a, b.c, d.e.f, d.g },
///   { a, b.c.d, b.c.e, d.e,h }
/// ) = { a, b.c }
fn filter_prefixes_of(left: &HashSet<vir::Place>, right: &HashSet<vir::Place>) -> HashSet<vir::Place> {
    let mut res = HashSet::new();
    for left_item in left.iter() {
        for right_item in right.iter() {
            if right_item.has_prefix(left_item) {
                res.insert(left_item.clone());
            }
        }
    }
    res
}

impl BranchCtxt {
    pub fn new(local_vars: Vec<vir::LocalVar>, predicates: HashMap<String, vir::Predicate>) -> Self {
        BranchCtxt {
            state: State::new(
                HashSet::from_iter(local_vars.into_iter().map(|v| vir::Place::Base(v))),
                HashSet::new()
            ),
            predicates
        }
    }

    /// Simulate an unfold
    fn unfold(&mut self, pred_place: &vir::Place) -> vir::Stmt {
        debug!("We want to unfold {:?}", pred_place);
        assert!(self.state.contains_acc(&pred_place));
        assert!(self.state.contains_pred(&pred_place));

        let predicate_name = pred_place.typed_ref_name().unwrap();
        let predicate = self.predicates.get(&predicate_name).unwrap();

        let pred_self_place: vir::Place = predicate.args[0].clone().into();
        let places_in_pred: Vec<AccOrPred> = predicate.get_contained_places().into_iter()
            .map( |aop| aop.map( |p|
                p.replace_prefix(&pred_self_place, pred_place.clone())
            )).collect();

        // Simulate unfolding of `pred_place`
        self.state.remove_pred(&pred_place);
        self.state.insert_all(places_in_pred.into_iter());

        debug!("We unfolded {:?}", pred_place);

        vir::Stmt::Unfold(predicate_name.clone(), vec![ pred_place.clone().into() ])
    }

    fn drop(&mut self, pred_place: &vir::Place) -> vir::Stmt {
        debug!("We want to drop {:?}", pred_place);
        assert!(self.state.pred().contains(&pred_place));

        let predicate_name = pred_place.typed_ref_name().unwrap();

        // Simulate exhaling/dropping of `pred_place`
        self.state.remove_pred(&pred_place);

        // Done.
        debug!("We dropped {:?}", pred_place);

        vir::Stmt::comment(
            format!("[foldunfold] Drop {}({})", predicate_name, pred_place)
        )
    }

    /// left is self, right is other
    pub fn join(&mut self, mut other: BranchCtxt) -> (Vec<vir::Stmt>, Vec<vir::Stmt>) {
        let mut left_stmts: Vec<vir::Stmt> = vec![];
        let mut right_stmts: Vec<vir::Stmt> = vec![];

        debug!("Join branches");
        trace!("Left branch: {:?}", self.state);
        trace!("Right branch: {:?}", other.state);
        assert!(self.state.consistent());

        if self.state.pred() != other.state.pred() {
            let maybe_preserved_left = filter_prefixes_of(self.state.pred(), other.state.acc());
            let maybe_preserved_right = filter_prefixes_of(other.state.pred(), self.state.acc());
            let maybe_preserved_pred: HashSet<_> = maybe_preserved_left.union(&maybe_preserved_right).cloned().collect();
            debug!("Maybe preserved predicates: {:?}", maybe_preserved_pred);

            let original_self_pred = self.state.pred().clone();
            let original_other_pred = other.state.pred().clone();

            for pred_place in &maybe_preserved_pred {
                debug!("Current predicate to agree on: {}", pred_place);

                // Obtain `pred_place` in both branches, or drop all suffixes of `pred_place`
                let self_initial_state = self.state.clone();
                let other_initial_state = other.state.clone();
                let self_stmts_opt = self.obtain_all(vec![AccOrPred::Pred(pred_place.clone())], false);
                let other_stmts_opt = other.obtain_all(vec![AccOrPred::Pred(pred_place.clone())], false);

                match (self_stmts_opt, other_stmts_opt) {
                    (Some(self_stmts), Some(other_stmts)) => {
                        // Obtain `pred_place` in both branches
                        left_stmts.extend(self_stmts);
                        right_stmts.extend(other_stmts);
                    },
                    _ => {
                        // Restore initial state
                        self.state = self_initial_state;
                        other.state = other_initial_state;
                        // Drop permissions
                        self.state.remove_pred_matching(|p| p.has_prefix(&pred_place));
                        other.state.remove_pred_matching(|p| p.has_prefix(&pred_place));
                        self.state.remove_acc_matching(|p| p.has_proper_prefix(&pred_place));
                        other.state.remove_acc_matching(|p| p.has_proper_prefix(&pred_place));
                    }
                }
            }

            // Drop predicates not in maybe_preserved_pred
            for pred_place in self.state.pred().clone().difference(&maybe_preserved_pred) {
                debug!("The left branch has an extra predicate: {}", pred_place);
                // We drop the permission.
                let stmt = self.drop(pred_place);
                left_stmts.push(stmt);
            }
            for pred_place in other.state.pred().clone().difference(&maybe_preserved_pred) {
                debug!("The right branch has an extra predicate: {}", pred_place);
                // We drop the permission.
                let stmt = other.drop(pred_place);
                right_stmts.push(stmt);
            }

            trace!("Statements in left branch: {:?}", &left_stmts);
            trace!("Statements in left branch: {:?}", &right_stmts);
        }

        self.state.intersect_acc(other.state.acc());
        assert!(self.state.consistent(), "Inconsistent state - Pred: {{{}}}, Acc: {{{}}}", self.state.display_pred(), self.state.display_acc());
        return (left_stmts, right_stmts);
    }

    /// Obtain the required permissions, changing the state inplace and returning the statements.
    /// If not possible, return None without changing the state.
    fn obtain_all(&mut self, reqs: Vec<AccOrPred>, force_fold: bool) -> Option<Vec<vir::Stmt>> {
        debug!("Obtain all: {{{}}}", display(&reqs));
        let original_state = self.state.clone();
        let mut stmts: Vec<vir::Stmt> = vec![];

        for req in &reqs {
            match self.obtain(req, force_fold) {
                Some(req_stmts) => {
                    stmts.extend(req_stmts);
                },
                None => {
                    if !force_fold {
                        self.state = original_state;
                        return None;
                    }
                }
            }
        }

        Some(stmts)
    }

    /// Obtain the required permission, changing the state inplace and returning the statements.
    /// If not possible, return None without changing the state.
    fn obtain(&mut self, req: &AccOrPred, force_fold: bool) -> Option<Vec<vir::Stmt>> {
        debug!("Obtain: {} - {:?}", req, req);

        let original_state = self.state.clone();
        let mut stmts: Vec<vir::Stmt> = vec![];

        trace!("Acc state: {{{}}}", self.state.display_debug_acc());
        trace!("Pred state: {{{}}}", self.state.display_debug_pred());

        let req_place = req.get_place();

        // Check if the requirement is satisfied
        if self.state.contains(req) {
            // `req` is satisfied, so we can remove it from `reqs`
            debug!("Requirement {} is satisfied", req);
            return Some(stmts);
        }

        debug!("Try to satisfy requirement {:?}", req);

        // Find a predicate on a prefix of req_place
        let existing_prefix_pred_opt: Option<vir::Place> = self.state.pred().iter()
            .find(|p| req_place.has_prefix(p))
            .cloned();

        match existing_prefix_pred_opt {
            Some(existing_pred_to_unfold) => {
                debug!("We want to unfold {:?}", existing_pred_to_unfold);
                let stmt = self.unfold(&existing_pred_to_unfold);
                stmts.push(stmt);
                debug!("We unfolded {:?}", existing_pred_to_unfold);
                // Check if we are done
                match self.obtain(req, force_fold) {
                    None => {
                        debug!("It is not possible to unfold {:?}", req_place);
                        self.state = original_state;
                        return None
                    },
                    Some(req_place_stmts) => {
                        stmts.extend(req_place_stmts);
                    }
                }
            },

            None => {
                match req {
                    AccOrPred::Pred(_) => {
                        // We want to fold `req_place`
                        debug!("We want to fold {:?}", req_place);
                        let predicate_name = req_place.typed_ref_name().unwrap();
                        let predicate = self.predicates.get(&predicate_name).unwrap();

                        let pred_self_place: vir::Place = predicate.args[0].clone().into();
                        let places_in_pred: Vec<AccOrPred> = predicate.get_contained_places().into_iter()
                            .map( |aop| aop.map( |p|
                                p.replace_prefix(&pred_self_place, req_place.clone())
                            )).collect();

                        // Find an access or predicate permission on a proper suffix of req_place
                        let existing_proper_suffix_perm_opt: Option<_> = self.state.find(
                            |p| p.has_proper_prefix(&req_place)
                        );

                        // Check if it is possible to fold, to avoid infinite recursion
                        let can_fold = match existing_proper_suffix_perm_opt {
                            Some(_) => true,
                            None => places_in_pred.is_empty(),
                        };

                        if can_fold {
                            for fold_req_place in &places_in_pred {
                                match self.obtain(fold_req_place, force_fold) {
                                    None => {
                                        if force_fold {
                                            debug!("We assume that requirement {:?} is not needed to fold {:?}", fold_req_place, req_place);
                                        } else {
                                            debug!("It is not possible to fold {:?}: missing requirement {:?}", req_place, fold_req_place);
                                            self.state = original_state;
                                            return None
                                        }
                                    },
                                    Some(req_place_stmts) => {
                                        stmts.extend(req_place_stmts);
                                    }
                                }
                            }

                            stmts.push(
                                vir::Stmt::Fold(predicate_name.clone(), vec![ req_place.clone().into() ])
                            );

                            // Simulate folding of `req_place`
                            if !force_fold {
                                assert!(self.state.contains_all(places_in_pred.iter()));
                            }
                            assert!(self.state.contains_acc(&req_place));
                            assert!(!self.state.contains_pred(&req_place));
                            self.state.remove_all(places_in_pred.iter());
                            self.state.insert_pred(req_place.clone());

                            // Done. Continue checking the remaining requirements
                            debug!("We folded {:?}", req_place);
                        } else {
                            debug!(
                                "It is not possible to obtain {:?} by folding or unfolding predicates. Predicates: {:?}",
                                req,
                                self.state.pred()
                            );
                            self.state = original_state;
                            return None
                        }
                    },

                    AccOrPred::Acc(_) => {
                        // We have no predicate to obtain the access permission `req`
                        debug!(
                            "There is no predicate to obtain {:?}. Predicates: {:?}",
                            req,
                            self.state.pred()
                        );
                        self.state = original_state;
                        return None
                    },
                }
            },
        }

        Some(stmts)
    }

    pub fn apply_stmt(&mut self, stmt: &vir::Stmt) -> Vec<vir::Stmt> {
        debug!("");
        debug!("Apply on stmt: {}", stmt);
        let required_places: Vec<AccOrPred> = stmt.get_required_places(&self.predicates).into_iter().collect();

        let mut stmts: Vec<vir::Stmt> = vec![];

        trace!("Acc state before: {{{}}}", self.state.display_acc());
        trace!("Pred state before: {{{}}}", self.state.display_pred());
        trace!("required_places: {{{}}}", display(&required_places));

        assert!(self.state.consistent());

        if !required_places.is_empty() {
            if DEBUG_FOLDUNFOLD {
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Access permissions: {{{}}}", self.state.display_acc())));
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Predicate permissions: {{{}}}", self.state.display_pred())));
            }

            // We can not assert this, because the state is an overapproximation
            //stmts.push(vir::Stmt::Assert(self.state.as_vir_expr(), vir::Id()));

            stmts.append(
                &mut self.obtain_all(required_places, true).unwrap()
            );
        }

        stmt.apply_on_state(&mut self.state, &self.predicates);

        trace!("Acc state after: {{{}}}", self.state.display_acc());
        trace!("Pred state after: {{{}}}", self.state.display_pred());

        assert!(self.state.consistent());

        stmts
    }

    pub fn apply_successor(&mut self, succ: &vir::Successor) -> Vec<vir::Stmt> {
        debug!("Apply succ: {:?}", succ);
        let exprs: Vec<&vir::Expr> = match succ {
            &vir::Successor::GotoSwitch(ref guarded_targets, _) => {
                guarded_targets.iter().map(|g| &g.0).collect()
            },
            &vir::Successor::GotoIf(ref expr, _, _) => vec![expr],
            _ => vec![]
        };

        let required_places: Vec<AccOrPred> = exprs.iter().flat_map(
            |e| e.get_required_places(&self.predicates).into_iter().collect::<Vec<AccOrPred>>()
        ).collect();

        let mut stmts: Vec<vir::Stmt> = vec![];

        trace!("Acc state before: {{{}}}", self.state.display_acc());
        trace!("Pred state before: {{{}}}", self.state.display_pred());

        assert!(self.state.consistent());

        if !required_places.is_empty() {
            if DEBUG_FOLDUNFOLD {
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Access permissions: {{{}}}", self.state.display_acc())));
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Predicate permissions: {{{}}}", self.state.display_pred())));
            }

            // We can not assert this, because the state is an overapproximation
            //stmts.push(vir::Stmt::Assert(self.state.as_vir_expr(), vir::Id()));

            stmts.append(
                &mut self.obtain_all(required_places, true).unwrap()
            );

        }

        trace!("Acc state after: {{{}}}", self.state.display_acc());
        trace!("Pred state after: {{{}}}", self.state.display_pred());

        assert!(self.state.consistent());

        stmts
    }
}
