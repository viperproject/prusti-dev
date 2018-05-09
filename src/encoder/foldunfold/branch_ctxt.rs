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

    fn join(&self, other: &BranchCtxt) -> (Vec<vir::Stmt>, Vec<vir::Stmt>) {
        if self.state == other.state {
            return (vec![], vec![]);
        } else {
            unimplemented!()
        }
    }

    fn obtain(&mut self, mut reqs: Vec<AccOrPred>) -> Vec<vir::Stmt> {
            let mut stmts: Vec<vir::Stmt> = vec![];

        while !reqs.is_empty() {
            debug!("Acc state: {{{}}}", self.state.display_acc());
            debug!("Pred state: {{{}}}", self.state.display_pred());
            debug!("Requirements: {{{}}}", display(&reqs));

            let curr_req = reqs.pop().unwrap();
            let req_place = curr_req.get_place();

            // Check if the requirement is satisfied
            match &curr_req {
                &AccOrPred::Acc(ref place) => {
                    if self.state.acc().contains(place) {
                        continue
                    }
                },
                &AccOrPred::Pred(ref place) => {
                    if self.state.pred().contains(place) {
                        continue
                    }
                }
            }

            // Find a predicate on a prefix of req_place
            let existing_pred_opt: Option<vir::Place> = self.state.pred().iter()
                .find(|p| req_place.has_prefix(p))
                .cloned();

            match existing_pred_opt {
                Some(existing_pred) => {
                    // We want to unfold `existing_pred`
                    debug!("We want to unfold {:?}", existing_pred);
                    let predicate_name = existing_pred.typed_ref_name().unwrap();
                    let predicate = self.predicates.get(&predicate_name).unwrap();

                    let pred_self_place: vir::Place = predicate.args[0].clone().into();
                    let places_in_pred: Vec<AccOrPred> = predicate.get_contained_places().into_iter()
                        .map( |aop| aop.map( |p|
                            p.replace_prefix(&pred_self_place, existing_pred.clone())
                        )).collect();

                    stmts.push(
                        vir::Stmt::Unfold(predicate_name.clone(), vec![ existing_pred.clone().into() ])
                    );

                    // Simulate unfolding of `exising_pred`
                    assert!(self.state.pred().contains(&existing_pred));
                    self.state.remove_pred(&existing_pred);
                    self.state.insert_all(places_in_pred.into_iter());

                    // Done. Continue checking the remaining requirements
                    debug!("We unfolded {:?}", existing_pred);
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
                            self.state.remove_all(places_in_pred.iter());
                            self.state.insert_pred(req_place.clone());

                            // Done. Continue checking the remaining requirements
                            debug!("We folded {:?}", req_place);
                        },

                        AccOrPred::Acc(_) => {
                            // Unreachable
                            assert!(false);
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
        debug!("Acc state before: {{{}}}", self.state.display_acc());
        debug!("Pred state before: {{{}}}", self.state.display_pred());
        let required_places: Vec<AccOrPred> = stmt.get_required_places().into_iter().collect();

        let mut stmts: Vec<vir::Stmt> = vec![];

        stmts.push(vir::Stmt::comment(format!("Access permissions: {{{}}}", self.state.display_acc())));
        stmts.push(vir::Stmt::comment(format!("Predicate permissions: {{{}}}", self.state.display_pred())));
        stmts.push(vir::Stmt::Assert(self.state.as_vir_expr(), vir::Id()));

        stmts.append(
            &mut self.obtain(required_places)
        );

        stmt.apply_on_state(&mut self.state);

        debug!("Acc state after: {{{}}}", self.state.display_acc());
        debug!("Pred state after: {{{}}}", self.state.display_pred());

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

        let mut stmts: Vec<vir::Stmt> = vec![];

        stmts.push(vir::Stmt::comment(format!("Access permissions: {{{}}}", self.state.display_acc())));
        stmts.push(vir::Stmt::comment(format!("Predicate permissions: {{{}}}", self.state.display_pred())));
        stmts.push(vir::Stmt::Assert(self.state.as_vir_expr(), vir::Id()));

        stmts.append(
            &mut self.obtain(
                exprs.iter().flat_map(
                    |e| e.get_required_places().into_iter().collect::<Vec<AccOrPred>>()
                ).collect()
            )
        );

        stmts
    }
}
