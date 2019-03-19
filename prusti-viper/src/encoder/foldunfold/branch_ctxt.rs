// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::foldunfold::permissions::*;
use encoder::foldunfold::state::*;
use encoder::foldunfold::action::*;
use encoder::vir;
use encoder::vir::PermAmount;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use encoder::foldunfold::places_utils::*;
use encoder::foldunfold::perm::PermIterator;
use utils::to_string::ToString;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchCtxt<'a> {
    state: State,
    /// The definition of the predicates
    predicates: &'a HashMap<String, vir::Predicate>
}

impl<'a> BranchCtxt<'a> {
    pub fn new(local_vars: Vec<vir::LocalVar>, predicates: &'a HashMap<String, vir::Predicate>) -> Self {
        BranchCtxt {
            state: State::new(
                HashMap::from_iter(local_vars.into_iter().map(|v| (vir::Expr::local(v), PermAmount::Write))),
                HashMap::new(),
                HashSet::new()
            ),
            predicates
        }
    }

    pub fn clone_clean(&self) -> Self {
        let mut new_bctxt = self.clone();
        let mut state = new_bctxt.mut_state();
        state.remove_all();
        new_bctxt
    }

    pub fn state(&self) -> &State {
        &self.state
    }

    pub fn mut_state(&mut self) -> &mut State {
        &mut self.state
    }

    pub fn predicates(&self) -> &HashMap<String, vir::Predicate> {
        self.predicates
    }

    /// Simulate an unfold
    fn unfold(&mut self, pred_place: &vir::Expr, perm_amount: PermAmount) -> Action {
        debug!("We want to unfold {} with {}", pred_place, perm_amount);
        //assert!(self.state.contains_acc(pred_place), "missing acc({}) in {}", pred_place, self.state);
        assert!(self.state.contains_pred(pred_place), "missing pred({}) in {}", pred_place, self.state);
        assert!(perm_amount.is_valid_for_specs(), "Invalid permission amount.");

        let predicate_name = pred_place.typed_ref_name().unwrap();
        let predicate = self.predicates.get(&predicate_name).unwrap();

        let pred_self_place: vir::Expr = predicate.args[0].clone().into();
        let places_in_pred: Vec<Perm> = predicate.get_permissions().into_iter()
            .map(
                |perm| {
                    perm.map_place(|p| p.replace_place(&pred_self_place, pred_place))
                        .update_perm_amount(perm_amount)
                }
            )
            .collect();

        trace!("Pred state before unfold: {{\n{}\n}}", self.state.display_pred());

        // Simulate unfolding of `pred_place`
        self.state.remove_pred(&pred_place, perm_amount);
        self.state.insert_all_perms(places_in_pred.into_iter());

        debug!("We unfolded {}", pred_place);

        trace!("Acc state after unfold: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state after unfold: {{\n{}\n}}", self.state.display_pred());

        Action::Unfold(predicate_name.clone(), vec![ pred_place.clone().into() ], perm_amount)
    }

    /// left is self, right is other
    pub fn join(&mut self, mut other: BranchCtxt) -> (Vec<Action>, Vec<Action>) {
        let mut left_actions: Vec<Action> = vec![];
        let mut right_actions: Vec<Action> = vec![];

        debug!("Join branches");
        trace!("Left branch: {:?}", self.state);
        trace!("Right branch: {:?}", other.state);
        self.state.check_consistency();

        // If they are already the same, avoid unnecessary operations
        if self.state != other.state {
            // Compute which paths are moved out
            /*
            let moved_paths: HashSet<_> = if anti_join {
                filter_with_prefix_in_other(
                    self.state.moved(),
                    other.state.moved()
                )
            } else {
                ancestors(
                    &self.state.moved().clone().union(other.state.moved()).cloned().collect()
                )
            };
            */
            let moved_paths: HashSet<_> = ancestors(
                &self.state.moved().clone().union(other.state.moved()).cloned().collect()
            );
            self.state.set_moved(moved_paths.clone());
            other.state.set_moved(moved_paths.clone());
            debug!("moved_paths: {:?}", moved_paths);

            trace!("left acc: {{\n{}\n}}", self.state.display_acc());
            trace!("right acc: {{\n{}\n}}", other.state.display_acc());

            trace!("left pred: {{\n{}\n}}", self.state.display_pred());
            trace!("right pred: {{\n{}\n}}", other.state.display_pred());

            trace!("left acc_leaves: {:?}", self.state.acc_leaves());
            trace!("right acc_leaves: {:?}", other.state.acc_leaves());

            // Compute which access permissions may be preserved
            let potential_acc: HashSet<_> = filter_with_prefix_in_other(&self.state.acc_leaves(), &other.state.acc_leaves());
            debug!("potential_acc: {:?}", potential_acc);

            // Remove access permissions that can not be obtained due to a moved path
            let actual_acc: HashSet<_> = filter_not_proper_extensions_of(&potential_acc, &moved_paths);
            debug!("actual_acc: {:?}", actual_acc);

            // Obtain access permissions
            for acc_place in &actual_acc {
                if !self.state.acc().contains_key(acc_place) {
                    debug!("The left branch needs to obtain an access permission: {}", acc_place);
                    let perm_amount = other.state.acc()[acc_place];
                    // Unfold something and get `acc_place`
                    left_actions.extend(
                        self.obtain(&Perm::acc(acc_place.clone(), perm_amount))
                    );
                }
                if !other.state.acc().contains_key(acc_place) {
                    debug!("The right branch needs to obtain an access permission: {}", acc_place);
                    let perm_amount = self.state.acc()[acc_place];
                    // Unfold something and get `acc_place`
                    right_actions.extend(
                        other.obtain(&Perm::acc(acc_place.clone(), perm_amount))
                    );
                }
            }

            // Drop predicate permissions that can not be obtained due to a move
            for pred_place in &filter_proper_extensions_of(&self.state.pred_places(), &moved_paths) {
                debug!("Drop pred {} in left branch (it is moved out in the other branch)", pred_place);
                assert!(self.state.pred().contains_key(&pred_place));
                let perm_amount = self.state.remove_pred_place(&pred_place);
                left_actions.push(
                    Action::Drop(Perm::pred(pred_place.clone(), perm_amount))
                );
            }
            for pred_place in &filter_proper_extensions_of(&other.state.pred_places(), &moved_paths) {
                debug!("Drop pred {} in right branch (it is moved out in the other branch)", pred_place);
                assert!(other.state.pred().contains_key(&pred_place));
                let perm_amount = other.state.remove_pred_place(&pred_place);
                right_actions.push(
                    Action::Drop(Perm::pred(pred_place.clone(), perm_amount))
                );
            }

            // Compute preserved predicate permissions
            let preserved_preds: HashSet<_> = intersection(&self.state.pred_places(), &other.state.pred_places());
            debug!("preserved_preds: {:?}", preserved_preds);

            // Drop predicate permissions that are not in the other branch
            for pred_place in self.state.pred_places().difference(&preserved_preds) {
                debug!("Drop pred {} in left branch (it is not in the other branch)", pred_place);
                assert!(self.state.pred().contains_key(&pred_place));
                let perm_amount = self.state.remove_pred_place(&pred_place);
                left_actions.push(
                    Action::Drop(Perm::pred(pred_place.clone(), perm_amount))
                );
            }
            for pred_place in other.state.pred_places().difference(&preserved_preds) {
                debug!("Drop pred {} in right branch (it is not in the other branch)", pred_place);
                assert!(other.state.pred().contains_key(&pred_place));
                let perm_amount = other.state.remove_pred_place(&pred_place);
                right_actions.push(
                    Action::Drop(Perm::pred(pred_place.clone(), perm_amount))
                );
            }

            // Drop access permissions that can not be obtained due to a move
            for acc_place in &filter_proper_extensions_of(&self.state.acc_places(), &moved_paths) {
                debug!("Drop acc {} in left branch (it is moved out in the other branch)", acc_place);
                assert!(self.state.acc().contains_key(&acc_place));
                let perm_amount = self.state.remove_acc_place(&acc_place);
                left_actions.push(
                    Action::Drop(Perm::acc(acc_place.clone(), perm_amount))
                );
            }
            for acc_place in &filter_proper_extensions_of(&other.state.acc_places(), &moved_paths) {
                debug!("Drop acc {} in right branch (it is moved out in the other branch)", acc_place);
                assert!(other.state.acc().contains_key(&acc_place));
                let perm_amount = other.state.remove_acc_place(&acc_place);
                right_actions.push(
                    Action::Drop(Perm::acc(acc_place.clone(), perm_amount))
                );
            }

            // Drop access permissions not in `actual_acc`
            for acc_place in filter_not_extensions_of(&self.state.acc_places(), &other.state.acc_places()) {
                debug!("Drop acc {} in left branch (it has no prefix in the other branch)", acc_place);
                assert!(self.state.acc().contains_key(&acc_place));
                let perm_amount = self.state.remove_acc_place(&acc_place);
                left_actions.push(
                    Action::Drop(Perm::acc(acc_place.clone(), perm_amount))
                );
            }
            for acc_place in filter_not_extensions_of(&other.state.acc_places(), &self.state.acc_places()) {
                debug!("Drop acc {} in right branch (it has no prefix in the other branch)", acc_place);
                assert!(other.state.acc().contains_key(&acc_place));
                let perm_amount = other.state.remove_acc_place(&acc_place);
                left_actions.push(
                    Action::Drop(Perm::acc(acc_place.clone(), perm_amount))
                );
            }

            trace!(
                "Actions in left branch: {}",
                left_actions.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", ")
            );
            trace!(
                "Actions in right branch: {}",
                right_actions.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", ")
            );

            assert_eq!(self.state.acc(), other.state.acc());
            assert_eq!(self.state.pred(), other.state.pred());
            self.state.check_consistency();
        }

        return (left_actions, right_actions);
    }

    /// Obtain the required permissions, changing the state inplace and returning the statements.
    fn obtain_all(&mut self, reqs: Vec<Perm>) -> Vec<Action> {
        debug!("[enter] obtain_all: {{{}}}", reqs.iter().to_string());
        reqs.iter()
            .flat_map(|perm| self.obtain(perm))
            .collect()
    }

    /// Obtain the required permission, changing the state inplace and returning the statements.
    fn obtain(&mut self, req: &Perm) -> Vec<Action> {
        trace!("[enter] obtain(req={})", req);

        let mut actions: Vec<Action> = vec![];

        trace!("Acc state before: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state before: {{\n{}\n}}", self.state.display_pred());

        // 1. Check if the requirement is satisfied
        if self.state.contains_perm(req) {
            // `req` is satisfied, so we can remove it from `reqs`
            trace!("[exit] obtain: Requirement {} is satisfied", req);
            return actions;
        }
        if req.is_acc() && req.is_local() {
            // access permissions on local variables are always satisfied
            trace!("[exit] obtain: Requirement {} is satisfied", req);
            return actions;
        }

        debug!("Try to satisfy requirement {}", req);

        // 3. Obtain with an unfold
        // Find a predicate on a proper prefix of req
        let existing_prefix_pred_opt: Option<vir::Expr> = self.state.pred_places().iter()
            .find(|p| req.has_proper_prefix(p))
            .cloned();
        if let Some(existing_pred_to_unfold) = existing_prefix_pred_opt {
            let perm_amount = self.state.pred()[&existing_pred_to_unfold];
            debug!("We want to unfold {} with permission {} (we need at least {})",
                   existing_pred_to_unfold, perm_amount, req.get_perm_amount());
            assert!(perm_amount >= req.get_perm_amount());
            let action = self.unfold(&existing_pred_to_unfold, perm_amount);
            actions.push(action);
            debug!("We unfolded {}", existing_pred_to_unfold);

            // Check if we are done
            actions.extend(self.obtain(req));
            trace!("[exit] obtain");
            return actions;
        }

        // 4. Obtain with a fold
        if req.is_pred() {
            // We want to fold `req`
            debug!("We want to fold {}", req);
            let predicate_name = req.typed_ref_name().unwrap();
            let predicate = self.predicates.get(&predicate_name).unwrap();

            let pred_self_place: vir::Expr = predicate.args[0].clone().into();
            let places_in_pred: Vec<Perm> = predicate.get_permissions().into_iter()
                .map(
                    |perm| {
                        perm.map_place( |p|
                            p.replace_place(&pred_self_place, req.get_place())
                        )
                    }
                ).collect();

            // Find an access permission for which req is a proper suffix
            let existing_proper_perm_extension_opt: Option<_> = self.state.acc_places().into_iter().find(
                |p| p.has_proper_prefix(req.get_place())
            );

            // Check that there exists something that would make the fold possible.
            // We don't want to end up in an infinite recursion, trying to obtain the
            // predicates in the body.
            let can_fold = match existing_proper_perm_extension_opt {
                Some(_) => true,
                None => places_in_pred.is_empty(),
            };

            if can_fold {
                let perm_amount = places_in_pred
                    .iter()
                    .map(|p| {
                        self.state
                            .acc().iter()
                            .chain(self.state.pred().iter())
                            .filter(|(place, _)| place.has_prefix(p.get_place()))
                            .map(|(place, perm_amount)| {
                                debug!("Place {} can offer {}", place, perm_amount);
                                *perm_amount
                            })
                            .min()
                            .unwrap_or(PermAmount::Write)
                }).min().unwrap_or(PermAmount::Write);
                debug!("We want to fold {} with permission {} (we need at least {})",
                       req, perm_amount, req.get_perm_amount());

                for fold_req_place in &places_in_pred {
                    actions.extend(self.obtain(&(fold_req_place.clone())));
                }

                let scaled_places_in_pred: Vec<_> = places_in_pred
                    .into_iter()
                    .map(|perm| perm.update_perm_amount(perm_amount))
                    .collect();

                actions.push(
                    Action::Fold(predicate_name.clone(), vec![ req.get_place().clone().into() ], perm_amount)
                );

                // Simulate folding of `req`
                assert!(self.state.contains_all_perms(scaled_places_in_pred.iter()));
                assert!(
                    !req.get_place().is_simple_place() || self.state.contains_acc(req.get_place()),
                    "req={} state={}",
                    req.get_place(),
                    self.state
                );
                assert!(!self.state.contains_pred(req.get_place()));
                self.state.remove_all_perms(scaled_places_in_pred.iter());
                self.state.insert_pred(req.get_place().clone(), perm_amount);

                // Done. Continue checking the remaining requirements
                debug!("We folded {}", req);
                trace!("[exit] obtain");
                return actions;
            }
        } else {
            // We have no predicate to obtain the access permission `req`
            unreachable!(
r"There is no access permission to obtain {} ({:?}).
Access permissions: {{
{}
}}

Predicates: {{
{}
}}
",
                req,
                req,
                self.state.display_acc(),
                self.state.display_pred()
            );
        };

        unreachable!(
r"It is not possible to obtain {} ({:?}).
Access permissions: {{
{}
}}

Predicates: {{
{}
}}
",
            req,
            req,
            self.state.display_acc(),
            self.state.display_pred()
        );
    }

    /// Returns some of the dropped permissions
    pub fn apply_stmt(&mut self, stmt: &vir::Stmt) {
        debug!("apply_stmt: {}", stmt);

        trace!("Acc state before: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state before: {{\n{}\n}}", self.state.display_pred());

        self.state.check_consistency();

        stmt.apply_on_state(&mut self.state, self.predicates);

        trace!("Acc state after: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state after: {{\n{}\n}}", self.state.display_pred());

        self.state.check_consistency();
    }

    pub fn obtain_permissions(&mut self, permissions: Vec<Perm>) -> Vec<Action> {
        trace!("[enter] obtain_permissions: {}", permissions.iter().to_string());

        trace!("Acc state before: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state before: {{\n{}\n}}", self.state.display_pred());

        self.state.check_consistency();

        let actions = self.obtain_all(permissions);

        trace!("Acc state after: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state after: {{\n{}\n}}", self.state.display_pred());

        self.state.check_consistency();

        trace!("[exit] obtain_permissions: {}", actions.iter().to_string());
        actions
    }
}
