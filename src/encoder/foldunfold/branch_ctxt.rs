// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::foldunfold::requirements::*;
use encoder::foldunfold::state::*;
use encoder::vir;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use encoder::foldunfold::places_utils::*;

const DEBUG_FOLDUNFOLD: bool = false;

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
                HashSet::new(),
                HashSet::new(),
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
        let places_in_pred: Vec<Perm> = predicate.get_contained_places().into_iter()
            .map( |aop| aop.map( |p|
                p.replace_prefix(&pred_self_place, pred_place.clone())
            )).collect();

        trace!("Pred state before unfold: {{{}}}", self.state.display_debug_pred());

        // Simulate unfolding of `pred_place`
        self.state.remove_pred(&pred_place);
        self.state.insert_all_perms(places_in_pred.into_iter());

        debug!("We unfolded {:?}", pred_place);

        trace!("Pred state after unfold: {{{}}}", self.state.display_debug_pred());

        vir::Stmt::Unfold(predicate_name.clone(), vec![ pred_place.clone().into() ])
    }

    /// left is self, right is other
    pub fn join(&mut self, mut other: BranchCtxt) -> (Vec<vir::Stmt>, Vec<vir::Stmt>) {
        let mut left_stmts: Vec<vir::Stmt> = vec![];
        let mut right_stmts: Vec<vir::Stmt> = vec![];

        debug!("Join branches");
        trace!("Left branch: {:?}", self.state);
        trace!("Right branch: {:?}", other.state);
        self.state.check_consistency();

        // If they are already the same, avoid unnecessary operations
        if self.state != other.state {
            // Compute which paths are moved out
            let moved_paths: HashSet<_> = self.state.moved().clone().union(other.state.moved()).cloned().collect();
            self.state.set_moved(moved_paths.clone());
            other.state.set_moved(moved_paths.clone());
            debug!("moved_paths: {:?}", moved_paths);

            trace!("left acc: {:?}", self.state.acc());
            trace!("right acc: {:?}", other.state.acc());

            trace!("left acc_leafes: {:?}", self.state.acc_leafes());
            trace!("right acc_leafes: {:?}", other.state.acc_leafes());

            // Compute which access permissions may be preserved
            let potential_acc: HashSet<_> = filter_with_prefix_in_other(&self.state.acc_leafes(), &other.state.acc_leafes());
            debug!("potential_acc: {:?}", potential_acc);

            // Remove access permissions that can not be obtained due to a moved path
            let actual_acc: HashSet<_> = filter_not_proper_extensions_of(&potential_acc, &moved_paths);
            debug!("actual_acc: {:?}", actual_acc);

            // Obtain access permissions
            for acc_place in &actual_acc {
                if !self.state.acc().contains(acc_place) {
                    debug!("The left branch needs to obtain an access permission: {}", acc_place);
                    // Unfold something and get `acc_place`
                    left_stmts.extend(
                        self.obtain(&Perm::Acc(acc_place.clone()))
                    );
                }
                if !other.state.acc().contains(acc_place) {
                    debug!("The right branch needs to obtain an access permission: {}", acc_place);
                    // Unfold something and get `acc_place`
                    right_stmts.extend(
                        other.obtain(&Perm::Acc(acc_place.clone()))
                    );
                }
            }

            // Drop predicate permissions that can not be obtained due to a move
            for pred_place in &filter_proper_extensions_of(self.state.pred(), &moved_paths) {
                debug!("Drop pred {} in left branch (it is moved out in the other branch)", pred_place);
                self.state.remove_pred(&pred_place);
            }
            for pred_place in &filter_proper_extensions_of(other.state.pred(), &moved_paths) {
                debug!("Drop pred {} in right branch (it is moved out in the other branch)", pred_place);
                other.state.remove_pred(&pred_place);
            }

            // Compute preserved predicate permissions
            let preserved_preds: HashSet<_> = intersection(self.state.pred(), other.state.pred());
            debug!("preserved_preds: {:?}", preserved_preds);

            // Drop predicate permissions that are not in the other branch
            for pred_place in self.state.pred().clone().difference(&preserved_preds) {
                debug!("Drop pred {} in left branch (it is not in the other branch)", pred_place);
                self.state.remove_pred(&pred_place);
            }
            for pred_place in other.state.pred().clone().difference(&preserved_preds) {
                debug!("Drop pred {} in right branch (it is not in the other branch)", pred_place);
                other.state.remove_pred(&pred_place);
            }

            // Drop access permissions that can not be obtained due to a move
            for acc_place in &filter_proper_extensions_of(self.state.acc(), &moved_paths) {
                debug!("Drop acc {} in left branch (it is moved out in the other branch)", acc_place);
                self.state.remove_acc(&acc_place);
            }
            for acc_place in &filter_proper_extensions_of(other.state.acc(), &moved_paths) {
                debug!("Drop acc {} in right branch (it is moved out in the other branch)", acc_place);
                other.state.remove_acc(&acc_place);
            }

            trace!("Statements in left branch: {:?}", &left_stmts);
            trace!("Statements in left branch: {:?}", &right_stmts);

            assert_eq!(self.state.acc(), other.state.acc());
            assert_eq!(self.state.pred(), other.state.pred());
            self.state.check_consistency();
        }

        return (left_stmts, right_stmts);
    }

    /// Obtain the required permissions, changing the state inplace and returning the statements.
    fn obtain_all(&mut self, reqs: Vec<Perm>) -> Vec<vir::Stmt> {
        debug!("Obtain all: {{{}}}", display(&reqs));
        let mut stmts: Vec<vir::Stmt> = vec![];

        for req in &reqs {
            stmts.extend(
                self.obtain(req)
            );
        }

        stmts
    }

    /// Obtain the required permission, changing the state inplace and returning the statements.
    fn obtain(&mut self, req: &Perm) -> Vec<vir::Stmt> {
        debug!("Obtain: {}", req);

        let mut stmts: Vec<vir::Stmt> = vec![];

        trace!("Acc state: {{{}}}", self.state.display_debug_acc());
        trace!("Pred state: {{{}}}", self.state.display_debug_pred());

        let req_place = req.get_place();

        // Check if the requirement is satisfied
        if self.state.contains_perm(req) {
            // `req` is satisfied, so we can remove it from `reqs`
            debug!("Requirement {} is satisfied", req);
            return stmts;
        }

        debug!("Try to satisfy requirement {:?}", req);

        // Find a predicate on a proper prefix of req_place
        let existing_prefix_pred_opt: Option<vir::Place> = self.state.pred().iter()
            .find(|p| req_place.has_proper_prefix(p))
            .cloned();

        // Obtain with an unfold
        if let Some(existing_pred_to_unfold) = existing_prefix_pred_opt {
            debug!("We want to unfold {:?}", existing_pred_to_unfold);
            let stmt = self.unfold(&existing_pred_to_unfold);
            stmts.push(stmt);
            debug!("We unfolded {:?}", existing_pred_to_unfold);

            // Check if we are done
            stmts.extend(self.obtain(req));

            return stmts;
        }

        // Obtain with a fold
        match req {
            Perm::Pred(_) => {
                // We want to fold `req_place`
                debug!("We want to fold {:?}", req_place);
                let predicate_name = req_place.typed_ref_name().unwrap();
                let predicate = self.predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: Vec<Perm> = predicate.get_contained_places().into_iter()
                    .map( |aop| aop.map( |p|
                        p.replace_prefix(&pred_self_place, req_place.clone())
                    )).collect();

                // Find an access permission for which req_place is a proper suffix
                let existing_proper_perm_extension_opt: Option<_> = self.state.acc().iter().find(
                    |p| p.has_proper_prefix(&req_place)
                );

                // Check that there exists something that would make the fold possible.
                // We don't want to end up in an infinite recursion, trying to obtain the
                // predicates in the body.
                let can_fold = match existing_proper_perm_extension_opt {
                    Some(_) => true,
                    None => places_in_pred.is_empty(),
                };

                if can_fold {
                    for fold_req_place in &places_in_pred {
                        stmts.extend(self.obtain(fold_req_place));
                    }

                    stmts.push(
                        vir::Stmt::Fold(predicate_name.clone(), vec![ req_place.clone().into() ])
                    );

                    // Simulate folding of `req_place`
                    assert!(self.state.contains_all_perms(places_in_pred.iter()));
                    assert!(self.state.contains_acc(&req_place));
                    assert!(!self.state.contains_pred(&req_place));
                    self.state.remove_all_perms(places_in_pred.iter());
                    self.state.insert_pred(req_place.clone());

                    // Done. Continue checking the remaining requirements
                    debug!("We folded {:?}", req_place);
                } else {
                    unreachable!(
                        "It is not possible to obtain {:?} by folding or unfolding predicates. Predicates: {:?}",
                        req,
                        self.state.pred()
                    );
                }
            },

            Perm::Acc(_) => {
                // We have no predicate to obtain the access permission `req`
                unreachable!(
                    "There is no predicate to obtain {:?}. Predicates: {:?}",
                    req,
                    self.state.pred()
                );
            },
        }

        stmts
    }

    pub fn apply_stmt(&mut self, stmt: &vir::Stmt) -> Vec<vir::Stmt> {
        debug!("");
        debug!("Apply on stmt: {}", stmt);
        let required_places: Vec<Perm> = stmt.get_required_places(&self.predicates).into_iter().collect();

        let mut stmts: Vec<vir::Stmt> = vec![];

        trace!("Acc state before: {{{}}}", self.state.display_acc());
        trace!("Pred state before: {{{}}}", self.state.display_pred());
        trace!("required_places: {{{}}}", display(&required_places));

        self.state.check_consistency();

        if !required_places.is_empty() {
            if DEBUG_FOLDUNFOLD {
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Access permissions: {{{}}}", self.state.display_acc())));
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Predicate permissions: {{{}}}", self.state.display_pred())));
            }

            //stmts.push(vir::Stmt::Assert(self.state.as_vir_expr(), vir::Position()));

            stmts.extend(
                self.obtain_all(required_places)
            );
        }

        stmt.apply_on_state(&mut self.state, &self.predicates);

        trace!("Acc state after: {{{}}}", self.state.display_acc());
        trace!("Pred state after: {{{}}}", self.state.display_pred());

        self.state.check_consistency();

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

        let required_places: Vec<Perm> = exprs.iter().flat_map(
            |e| e.get_required_places(&self.predicates).into_iter().collect::<Vec<Perm>>()
        ).collect();

        let mut stmts: Vec<vir::Stmt> = vec![];

        trace!("Acc state before: {{{}}}", self.state.display_acc());
        trace!("Pred state before: {{{}}}", self.state.display_pred());

        self.state.check_consistency();

        if !required_places.is_empty() {
            if DEBUG_FOLDUNFOLD {
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Access permissions: {{{}}}", self.state.display_acc())));
                stmts.push(vir::Stmt::comment(format!("[foldunfold] Predicate permissions: {{{}}}", self.state.display_pred())));
            }

            //stmts.push(vir::Stmt::Assert(self.state.as_vir_expr(), vir::Position()));

            stmts.extend(
                self.obtain_all(required_places)
            );
        }

        trace!("Acc state after: {{{}}}", self.state.display_acc());
        trace!("Pred state after: {{{}}}", self.state.display_pred());

        self.state.check_consistency();

        stmts
    }
}
