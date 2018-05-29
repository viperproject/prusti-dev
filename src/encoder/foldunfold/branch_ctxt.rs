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

    fn exhale(&mut self, pred_place: &vir::Place) -> vir::Stmt {
        debug!("We want to exhale/drop {:?}", pred_place);
        assert!(self.state.pred().contains(&pred_place));

        let predicate_name = pred_place.typed_ref_name().unwrap();

        // Simulate exhaling/dropping of `pred_place`
        self.state.remove_pred(&pred_place);

        // Done.
        debug!("We exhaled/dropped {:?}", pred_place);

        vir::Stmt::Exhale(
            vir::Expr::PredicateAccessPredicate(
                box vir::Expr::PredicateAccess(
                    predicate_name.clone(),
                    vec![ pred_place.clone().into() ]
                ),
                vir::Perm::full()
            ),
            vir::Id()
        )
    }

    pub fn join(&mut self, mut other: BranchCtxt) -> (Vec<vir::Stmt>, Vec<vir::Stmt>) {
        let mut left_stmts: Vec<vir::Stmt> = vec![];
        let mut right_stmts: Vec<vir::Stmt> = vec![];

        loop {
            debug!("Iteration for join");

            debug!("Predicates in left branch: {:?}", self.state.pred());
            debug!("Predicates in right branch: {:?}", other.state.pred());
            assert!(self.state.consistent());

            if self.state.pred() == other.state.pred() {
                self.state.intersect_acc(other.state.acc());
                assert!(self.state.consistent());
                return (left_stmts, right_stmts);
            } else {
                debug!("self state: {:?}", self.state);
                debug!("other state: {:?}", other.state);

                let preserved_pred = definitely_preserved(self.state.pred(), other.state.pred());
                debug!("Preserved predicates: {:?}", preserved_pred);

                let original_self_pred = self.state.pred().clone();
                let original_other_pred = other.state.pred().clone();

                for pred_place in original_self_pred.difference(&preserved_pred) {
                    debug!("The left branch has an extra predicate: {}", pred_place);
                    if other.state.is_proper_prefix_of_some_acc(pred_place) {
                        // Unfold `pred_place`
                        let stmt = self.unfold(pred_place);
                        left_stmts.push(stmt);
                    } else {
                        // Here it's better not to unfold `x`, because it may be a recursive
                        // data structure and we may end up unfolding forever.
                        // So, we drop or exhale the permission.
                        let stmt = self.exhale(pred_place);
                        left_stmts.push(stmt);
                    }
                }

                for pred_place in original_other_pred.difference(&preserved_pred) {
                    debug!("The right branch has an extra predicate: {}", pred_place);
                    if self.state.is_proper_prefix_of_some_acc(pred_place) {
                        // Unfold `pred_place`
                        let stmt = other.unfold(pred_place);
                        right_stmts.push(stmt);
                    } else {
                        // Here it's better not to unfold `x`, because it may be a recursive
                        // data structure and we may end up unfolding forever.
                        // So, we drop or exhale the permission.
                        let stmt = other.exhale(pred_place);
                        right_stmts.push(stmt);
                    }
                }

                // Iterate once more, to check that self.state == other.state
                trace!("Statements in left branch: {:?}", &left_stmts);
                trace!("Statements in left branch: {:?}", &right_stmts);
            }
        }
    }

    fn obtain(&mut self, mut reqs: Vec<AccOrPred>) -> Vec<vir::Stmt> {
        debug!("Obtain: {{{}}}", display(&reqs));

        let mut stmts: Vec<vir::Stmt> = vec![];

        while !reqs.is_empty() {
            debug!("Acc state: {{{}}}", self.state.display_debug_acc());
            debug!("Pred state: {{{}}}", self.state.display_debug_pred());
            debug!("Requirements: {{{}}}", display(&reqs));

            let curr_req = &reqs[reqs.len() - 1];
            let req_place = curr_req.get_place();

            // Check if the requirement is satisfied
            if self.state.contains(curr_req) {
                // `curr_req` is satisfied, so we can remove it from `reqs`
                debug!("Requirement {} is satisfied", curr_req);
                reqs.pop();
                continue
            }

            debug!("Try to satisfy requirement {:?}", curr_req);

            // Find a predicate on a prefix of req_place
            let existing_pred_opt: Option<vir::Place> = self.state.pred().iter()
                .find(|p| req_place.has_prefix(p))
                .cloned();

            match existing_pred_opt {
                Some(existing_pred) => {
                    debug!("We want to unfold {:?}", existing_pred);
                    let stmt = self.unfold(&existing_pred);
                    stmts.push(stmt);
                    debug!("We unfold {:?}", existing_pred);
                    // Continue checking the remaining requirements
                },

                None => {
                    match curr_req {
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

                            stmts.append(
                                &mut self.obtain(places_in_pred.clone())
                            );

                            stmts.push(
                                vir::Stmt::Fold(predicate_name.clone(), vec![ req_place.clone().into() ])
                            );

                            // Simulate folding of `req_place`
                            assert!(self.state.contains_acc(&req_place));
                            self.state.remove_all(places_in_pred.iter());
                            self.state.insert_pred(req_place.clone());

                            // Done. Continue checking the remaining requirements
                            debug!("We folded {:?}", req_place);
                        },

                        AccOrPred::Acc(_) => {
                            // Unreachable
                            // We have no predicate to obtain the access permission `curr_req`
                            unreachable!(
                                    "There is no predicate to obtain {:?}. Predicates: {:?}",
                                    curr_req,
                                    self.state.pred()
                            );
                        },
                    }
                }
            }
        }

        stmts
    }

    pub fn apply_stmt(&mut self, stmt: &vir::Stmt) -> Vec<vir::Stmt> {
        debug!("");
        debug!("Apply on stmt: {}", stmt);
        let required_places: Vec<AccOrPred> = stmt.get_required_places(&self.predicates).into_iter().collect();

        let mut stmts: Vec<vir::Stmt> = vec![];

        debug!("Acc state before: {{{}}}", self.state.display_acc());
        debug!("Pred state before: {{{}}}", self.state.display_pred());

        assert!(self.state.consistent());

        if !required_places.is_empty() {
            //stmts.push(vir::Stmt::comment(format!("Access permissions: {{{}}}", self.state.display_acc())));
            //stmts.push(vir::Stmt::comment(format!("Predicate permissions: {{{}}}", self.state.display_pred())));

            // We can not assert this, because the state is an overapproximation
            //stmts.push(vir::Stmt::Assert(self.state.as_vir_expr(), vir::Id()));

            stmts.append(
                &mut self.obtain(required_places)
            );
        }

        stmt.apply_on_state(&mut self.state, &self.predicates);

        debug!("Acc state after: {{{}}}", self.state.display_acc());
        debug!("Pred state after: {{{}}}", self.state.display_pred());

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

        debug!("Acc state before: {{{}}}", self.state.display_acc());
        debug!("Pred state before: {{{}}}", self.state.display_pred());

        assert!(self.state.consistent());

        if !required_places.is_empty() {
            //stmts.push(vir::Stmt::comment(format!("Access permissions: {{{}}}", self.state.display_acc())));
            //stmts.push(vir::Stmt::comment(format!("Predicate permissions: {{{}}}", self.state.display_pred())));

            // We can not assert this, because the state is an overapproximation
            //stmts.push(vir::Stmt::Assert(self.state.as_vir_expr(), vir::Id()));

            stmts.append(
                &mut self.obtain(required_places)
            );

        }

        debug!("Acc state after: {{{}}}", self.state.display_acc());
        debug!("Pred state after: {{{}}}", self.state.display_pred());

        assert!(self.state.consistent());

        stmts
    }
}
