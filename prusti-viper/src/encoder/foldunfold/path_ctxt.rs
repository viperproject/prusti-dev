// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::foldunfold::{
    action::*, footprint::*, log::EventLog, perm::*, places_utils::*, requirements::*,
    semantics::ApplyOnState, state::*, FoldUnfoldError, FoldUnfoldError::FailedToObtain,
};
use log::{debug, trace};
use prusti_common::utils::to_string::ToString;
use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
};
use vir_crate::polymorphic::{self as vir, PermAmount};

/// The fold-unfold context of a CFG path
#[derive(Debug, Clone)]
pub struct PathCtxt<'a> {
    state: State,
    /// The definition of the predicates
    predicates: &'a HashMap<String, vir::Predicate>,
    /// All usages of old expressions to consider
    old_exprs: &'a HashMap<String, Vec<vir::Expr>>,
    /// A log of some of the relevant actions that lead to this fold-unfold context
    log: EventLog,
}

impl<'a> PathCtxt<'a> {
    pub fn new(
        local_vars: Vec<vir::LocalVar>,
        predicates: &'a HashMap<String, vir::Predicate>,
        old_exprs: &'a HashMap<String, Vec<vir::Expr>>,
    ) -> Self {
        PathCtxt {
            state: State::new(
                HashMap::from_iter(
                    local_vars
                        .into_iter()
                        .map(|v| (vir::Expr::local(v), PermAmount::Write)),
                ),
                HashMap::new(),
                HashSet::new(),
            ),
            predicates,
            old_exprs,
            log: EventLog::new(),
        }
    }

    pub(super) fn log_mut(&mut self) -> &mut EventLog {
        &mut self.log
    }

    pub(super) fn log(&self) -> &EventLog {
        &self.log
    }

    fn drain_log(self) -> EventLog {
        self.log
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

    pub fn old_exprs(&self) -> &HashMap<String, Vec<vir::Expr>> {
        self.old_exprs
    }

    /// Simulate an unfold
    fn unfold(
        &mut self,
        pred_place: &vir::Expr,
        perm_amount: PermAmount,
        variant: vir::MaybeEnumVariantIndex,
    ) -> Result<Action, FoldUnfoldError> {
        trace!("We want to unfold {} with {}", pred_place, perm_amount);
        //assert!(self.state.contains_acc(pred_place), "missing acc({}) in {}", pred_place, self.state);
        assert!(
            self.state.contains_pred(pred_place),
            "missing pred({}) in {}",
            pred_place,
            self.state
        );
        assert!(
            perm_amount.is_valid_for_specs(),
            "Invalid permission amount."
        );

        let predicate_name = pred_place.typed_ref_name().unwrap();
        let predicate = self
            .predicates
            .get(&predicate_name)
            .map(Ok)
            .unwrap_or_else(|| Err(FoldUnfoldError::MissingPredicate(predicate_name.clone())))?;

        let pred_self_place: vir::Expr = predicate.self_place();

        trace!(
            "Pred state before unfold: {{\n{}\n}}",
            self.state.display_pred()
        );

        // Simulate unfolding of `pred_place`
        self.state.remove_pred(pred_place, perm_amount)?;
        self.state
            .insert_all_perms(
                predicate
                    .get_body_footprint(&variant)
                    .into_iter()
                    .map(|perm| {
                        // TODO polymorphic
                        perm.map_place(|p| p.replace_place(&pred_self_place, pred_place))
                            .update_perm_amount(perm_amount)
                    }),
            )?;

        trace!("We unfolded {}", pred_place);

        trace!(
            "Acc state after unfold: {{\n{}\n}}",
            self.state.display_acc()
        );
        trace!(
            "Pred state after unfold: {{\n{}\n}}",
            self.state.display_pred()
        );

        Ok(Action::Unfold(vir::Unfold {
            predicate_name: predicate_name.clone(),
            arguments: vec![pred_place.clone()],
            permission: perm_amount,
            enum_variant: variant,
        }))
    }

    /// left is self, right is other
    /// Note: this merges the event logs as well
    pub fn join(
        &mut self,
        mut other: PathCtxt,
    ) -> Result<(Vec<Action>, Vec<Action>), FoldUnfoldError> {
        let mut left_actions: Vec<Action> = vec![];
        let mut right_actions: Vec<Action> = vec![];

        trace!("Join branches");
        trace!("Left branch: {}", self.state);
        trace!("Right branch: {}", other.state);
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
            // TODO: Remove all paths that are not definitely initialised.
            let moved_paths: HashSet<_> = ancestors(
                &self
                    .state
                    .moved()
                    .clone()
                    .union(other.state.moved())
                    .cloned()
                    .collect(),
            );
            self.state.set_moved(moved_paths.clone());
            other.state.set_moved(moved_paths.clone());
            trace!("moved_paths: {}", moved_paths.iter().to_string());

            trace!("left acc: {{\n{}\n}}", self.state.display_acc());
            trace!("right acc: {{\n{}\n}}", other.state.display_acc());

            trace!("left pred: {{\n{}\n}}", self.state.display_pred());
            trace!("right pred: {{\n{}\n}}", other.state.display_pred());

            trace!(
                "left acc_leaves: {}",
                self.state.acc_leaves().iter().to_sorted_multiline_string()
            );
            trace!(
                "right acc_leaves: {}",
                other.state.acc_leaves().iter().to_sorted_multiline_string()
            );

            // Compute which access permissions may be preserved
            let (unfold_potential_acc, fold_potential_pred) =
                compute_fold_target(&self.state.acc_places(), &other.state.acc_places());
            trace!(
                "unfold_potential_acc: {}",
                unfold_potential_acc.iter().to_sorted_multiline_string()
            );
            trace!(
                "fold_potential_pred: {}",
                fold_potential_pred.iter().to_sorted_multiline_string()
            );

            // Remove access permissions that can not be obtained due to a moved path
            let unfold_actual_acc =
                filter_not_proper_extensions_of(&unfold_potential_acc, &moved_paths);
            trace!(
                "unfold_actual_acc: {}",
                unfold_actual_acc.iter().to_sorted_multiline_string()
            );
            let fold_actual_pred =
                filter_not_proper_extensions_of(&fold_potential_pred, &moved_paths);
            trace!(
                "fold_actual_pred: {}",
                fold_actual_pred.iter().to_sorted_multiline_string()
            );

            // Obtain predicates by folding.
            for pred_place in fold_actual_pred {
                trace!("try to obtain predicate: {}", pred_place);
                let get_perm_amount = |ctxt: &PathCtxt| {
                    ctxt.state
                        .acc()
                        .iter()
                        .find(|(place, _)| place.has_proper_prefix(&pred_place))
                        .map(|(_, &perm_amount)| perm_amount)
                };
                let perm_amount = get_perm_amount(self)
                    .or_else(|| get_perm_amount(&other))
                    .unwrap();
                let pred_perm = Perm::pred(pred_place.clone(), perm_amount);
                let try_obtain = |left_ctxt: &mut PathCtxt,
                                  right_ctxt: &mut PathCtxt,
                                  left_actions: &mut Vec<_>,
                                  right_actions: &mut Vec<_>|
                 -> Result<(), FoldUnfoldError> {
                    match left_ctxt.obtain(&pred_perm, true)? {
                        ObtainResult::Success(new_actions) => {
                            left_actions.extend(new_actions);
                        }
                        ObtainResult::Failure(missing_perm) => {
                            trace!(
                                "Failed to obtain: {} because of {}",
                                pred_perm,
                                missing_perm
                            );
                            let remove_places = |ctxt: &mut PathCtxt, actions: &mut Vec<_>| {
                                ctxt.state.remove_moved_matching(|moved_place| {
                                    moved_place.has_prefix(&pred_place)
                                });
                                for acc_place in ctxt.state.acc_places() {
                                    if acc_place.has_proper_prefix(&pred_place) {
                                        let perm_amount = ctxt.state.remove_acc_place(&acc_place);
                                        let perm = Perm::acc(acc_place, perm_amount);
                                        trace!(
                                            "dropping perm={} missing_perm={}",
                                            perm,
                                            missing_perm
                                        );
                                        actions.push(Action::Drop(perm, missing_perm.clone()));
                                    }
                                }
                                for place in ctxt.state.pred_places() {
                                    if place.has_prefix(&pred_place) {
                                        let perm_amount = ctxt.state.remove_pred_place(&place);
                                        let perm = Perm::pred(place, perm_amount);
                                        trace!(
                                            "dropping perm={} missing_perm={}",
                                            perm,
                                            missing_perm
                                        );
                                        actions.push(Action::Drop(perm, missing_perm.clone()));
                                    }
                                }
                            };
                            remove_places(left_ctxt, left_actions);
                            remove_places(right_ctxt, right_actions);
                        }
                    }
                    Ok(())
                };
                try_obtain(self, &mut other, &mut left_actions, &mut right_actions)?;
                try_obtain(&mut other, self, &mut right_actions, &mut left_actions)?;
            }
            // Obtain access permissions by unfolding
            for acc_place in &unfold_actual_acc {
                let try_obtain = |ctxt_left: &mut PathCtxt,
                                  ctxt_right: &mut PathCtxt,
                                  left_actions: &mut Vec<_>,
                                  right_actions: &mut Vec<_>|
                 -> Result<bool, FoldUnfoldError> {
                    if !ctxt_left.state.acc().contains_key(acc_place) {
                        trace!(
                            "The left branch needs to obtain an access permission: {}",
                            acc_place
                        );
                        let perm_amount = ctxt_right.state.acc()[acc_place];
                        // Unfold something and get `acc_place`
                        let perm = Perm::acc(acc_place.clone(), perm_amount);
                        match ctxt_left.obtain(&perm, true)? {
                            ObtainResult::Success(new_actions) => {
                                left_actions.extend(new_actions);
                                Ok(true)
                            }
                            ObtainResult::Failure(missing_perm) => {
                                ctxt_right.state.remove_perm(&perm)?;
                                right_actions.push(Action::Drop(perm, missing_perm));
                                Ok(false)
                            }
                        }
                    } else {
                        Ok(true)
                    }
                };
                if try_obtain(self, &mut other, &mut left_actions, &mut right_actions)? {
                    try_obtain(&mut other, self, &mut right_actions, &mut left_actions)?;
                }
            }

            // Drop predicate permissions that can not be obtained due to a move
            for pred_place in &filter_proper_extensions_of(&self.state.pred_places(), &moved_paths)
            {
                trace!(
                    "Drop pred {} in left branch (it is moved out in the other branch)",
                    pred_place
                );
                assert!(self.state.pred().contains_key(pred_place));
                let perm_amount = self.state.remove_pred_place(pred_place);
                let perm = Perm::pred(pred_place.clone(), perm_amount);
                left_actions.push(Action::Drop(perm.clone(), perm));
            }
            for pred_place in &filter_proper_extensions_of(&other.state.pred_places(), &moved_paths)
            {
                trace!(
                    "Drop pred {} in right branch (it is moved out in the other branch)",
                    pred_place
                );
                assert!(other.state.pred().contains_key(pred_place));
                let perm_amount = other.state.remove_pred_place(pred_place);
                let perm = Perm::pred(pred_place.clone(), perm_amount);
                right_actions.push(Action::Drop(perm.clone(), perm));
            }

            // Compute preserved predicate permissions
            let preserved_preds: HashSet<_> =
                intersection(&self.state.pred_places(), &other.state.pred_places());
            trace!("preserved_preds: {}", preserved_preds.iter().to_string());

            // Drop predicate permissions that are not in the other branch
            for pred_place in self.state.pred_places().difference(&preserved_preds) {
                trace!(
                    "Drop pred {} in left branch (it is not in the other branch)",
                    pred_place
                );
                assert!(self.state.pred().contains_key(pred_place));
                let perm_amount = self.state.remove_pred_place(pred_place);
                let perm = Perm::pred(pred_place.clone(), perm_amount);
                left_actions.push(Action::Drop(perm.clone(), perm));
            }
            for pred_place in other.state.pred_places().difference(&preserved_preds) {
                trace!(
                    "Drop pred {} in right branch (it is not in the other branch)",
                    pred_place
                );
                assert!(other.state.pred().contains_key(pred_place));
                let perm_amount = other.state.remove_pred_place(pred_place);
                let perm = Perm::pred(pred_place.clone(), perm_amount);
                right_actions.push(Action::Drop(perm.clone(), perm));
            }

            // Drop access permissions that can not be obtained due to a move
            for acc_place in &filter_proper_extensions_of(&self.state.acc_places(), &moved_paths) {
                trace!(
                    "Drop acc {} in left branch (it is moved out in the other branch)",
                    acc_place
                );
                assert!(self.state.acc().contains_key(acc_place));
                let perm_amount = self.state.remove_acc_place(acc_place);
                let perm = Perm::acc(acc_place.clone(), perm_amount);
                left_actions.push(Action::Drop(perm.clone(), perm));
            }
            for acc_place in &filter_proper_extensions_of(&other.state.acc_places(), &moved_paths) {
                trace!(
                    "Drop acc {} in right branch (it is moved out in the other branch)",
                    acc_place
                );
                assert!(other.state.acc().contains_key(acc_place));
                let perm_amount = other.state.remove_acc_place(acc_place);
                let perm = Perm::acc(acc_place.clone(), perm_amount);
                right_actions.push(Action::Drop(perm.clone(), perm));
            }

            // Drop access permissions not in `actual_acc`
            for acc_place in self
                .state
                .acc_places()
                .difference(&other.state.acc_places())
            {
                trace!(
                    "Drop acc {} in left branch (not present in the other branch)",
                    acc_place
                );
                assert!(self.state.acc().contains_key(acc_place));
                let perm_amount = self.state.remove_acc_place(acc_place);
                self.state
                    .remove_moved_matching(|moved_place| moved_place.has_prefix(acc_place));
                let perm = Perm::acc(acc_place.clone(), perm_amount);
                left_actions.push(Action::Drop(perm.clone(), perm));
            }
            for acc_place in other
                .state
                .acc_places()
                .difference(&self.state.acc_places())
            {
                trace!(
                    "Drop acc {} in right branch (not present in the other branch)",
                    acc_place
                );
                assert!(other.state.acc().contains_key(acc_place));
                let perm_amount = other.state.remove_acc_place(acc_place);
                other
                    .state
                    .remove_moved_matching(|moved_place| moved_place.has_prefix(acc_place));
                let perm = Perm::acc(acc_place.clone(), perm_amount);
                right_actions.push(Action::Drop(perm.clone(), perm));
            }

            // If we have `Read` and `Write`, make both `Read`.
            for acc_place in self.state.acc_places() {
                assert!(
                    other.state.acc().contains_key(&acc_place),
                    "acc_place = {}",
                    acc_place
                );
                let left_perm = self.state.acc()[&acc_place];
                let right_perm = other.state.acc()[&acc_place];
                if left_perm == PermAmount::Write && right_perm == PermAmount::Read {
                    self.state.remove_acc(&acc_place, PermAmount::Remaining)?;
                    let perm = Perm::acc(acc_place.clone(), PermAmount::Remaining);
                    left_actions.push(Action::Drop(perm.clone(), perm));
                }
                if left_perm == PermAmount::Read && right_perm == PermAmount::Write {
                    other.state.remove_acc(&acc_place, PermAmount::Remaining)?;
                    let perm = Perm::acc(acc_place.clone(), PermAmount::Remaining);
                    right_actions.push(Action::Drop(perm.clone(), perm));
                }
            }
            for pred_place in self.state.pred_places() {
                assert!(other.state.pred().contains_key(&pred_place));
                let left_perm = self.state.pred()[&pred_place];
                let right_perm = other.state.pred()[&pred_place];
                if left_perm == PermAmount::Write && right_perm == PermAmount::Read {
                    self.state.remove_pred(&pred_place, PermAmount::Remaining)?;
                    let perm = Perm::pred(pred_place.clone(), PermAmount::Remaining);
                    left_actions.push(Action::Drop(perm.clone(), perm));
                }
                if left_perm == PermAmount::Read && right_perm == PermAmount::Write {
                    other
                        .state
                        .remove_pred(&pred_place, PermAmount::Remaining)?;
                    let perm = Perm::pred(pred_place.clone(), PermAmount::Remaining);
                    right_actions.push(Action::Drop(perm.clone(), perm));
                }
            }

            trace!(
                "Actions in left branch: \n{}",
                left_actions
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(",\n")
            );
            trace!(
                "Actions in right branch: \n{}",
                right_actions
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(",\n")
            );

            assert_eq!(self.state.acc(), other.state.acc());
            assert_eq!(self.state.pred(), other.state.pred());
            self.state.check_consistency();
        }

        // Merge the event logs
        self.log_mut().join(other.drain_log())?;

        Ok((left_actions, right_actions))
    }

    /// Obtain the required permissions, changing the state inplace and returning the statements.
    fn obtain_all(&mut self, reqs: Vec<Perm>) -> Result<Vec<Action>, FoldUnfoldError> {
        trace!("[enter] obtain_all: {{{}}}", reqs.iter().to_string());
        reqs.iter()
            .map(|perm| self.obtain(perm, false).and_then(|x| x.get_actions()))
            .collect::<Result<Vec<Vec<Action>>, _>>()
            .map(|res: Vec<Vec<Action>>| res.into_iter().flatten().collect())
    }

    /// Obtain the required permission, changing the state inplace and returning the statements.
    ///
    /// ``in_join`` – are we currently trying to join branches?
    fn obtain(&mut self, req: &Perm, in_join: bool) -> Result<ObtainResult, FoldUnfoldError> {
        trace!("[enter] obtain(req={})", req);

        let mut actions: Vec<Action> = vec![];

        trace!("Acc state before: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state before: {{\n{}\n}}", self.state.display_pred());

        // 1. Check if the requirement is satisfied
        if self.state.contains_perm(req) {
            trace!("[exit] obtain: Requirement {} is satisfied", req);
            return Ok(ObtainResult::Success(actions));
        }
        if req.is_acc() && req.is_local() {
            // access permissions on local variables are always satisfied
            trace!("[exit] obtain: Requirement {} is satisfied", req);
            return Ok(ObtainResult::Success(actions));
        }

        trace!("Try to satisfy requirement {}", req);

        // 3. Obtain with an unfold
        // Find a predicate on a proper prefix of req
        let existing_prefix_pred_opt: Option<vir::Expr> = self
            .state
            .pred_places()
            .iter()
            .find(|p| req.has_proper_prefix(p))
            .cloned();
        if let Some(existing_pred_to_unfold) = existing_prefix_pred_opt {
            let perm_amount = self.state.pred()[&existing_pred_to_unfold];
            trace!(
                "We want to unfold {} with permission {} (we need at least {})",
                existing_pred_to_unfold,
                perm_amount,
                req.get_perm_amount()
            );
            assert!(
                perm_amount >= req.get_perm_amount(),
                "perm_amount is {}, but it should be >= {}",
                perm_amount,
                req.get_perm_amount(),
            );
            let variant = find_variant(&existing_pred_to_unfold, req.get_place());
            let action = self.unfold(&existing_pred_to_unfold, perm_amount, variant)?;
            actions.push(action);
            trace!("We unfolded {}", existing_pred_to_unfold);

            // Check if we are done
            let new_actions = self.obtain(req, false)?.get_actions()?;
            actions.extend(new_actions);
            trace!("[exit] obtain");
            return Ok(ObtainResult::Success(actions));
        }

        // 4. Obtain with a fold
        if req.is_pred() {
            // We want to fold `req`
            trace!("We want to fold {}", req);
            let predicate_name = req.typed_ref_name().unwrap();
            let predicate = self.predicates.get(&predicate_name).unwrap();

            let variant = find_unfolded_variant(&self.state, req.get_place());

            // Find an access permission for which req is a proper suffix
            let existing_proper_perm_extension_opt: Option<_> = self
                .state
                .acc_places()
                .into_iter()
                .find(|p| p.has_proper_prefix(req.get_place()));

            let pred_self_place: vir::Expr = predicate.self_place();

            // TODO polymorphic
            let places_in_pred: Vec<Perm> = predicate
                .get_body_footprint(&variant)
                .into_iter()
                .map(|perm| perm.map_place(|p| p.replace_place(&pred_self_place, req.get_place())))
                .collect();

            // Check that there exists something that would make the fold possible.
            // We don't want to end up in an infinite recursion, trying to obtain the
            // predicates in the body.
            let can_fold = match existing_proper_perm_extension_opt {
                Some(_) => true,
                None => places_in_pred.is_empty() && !predicate.is_abstract(),
            };

            if can_fold {
                let perm_amount = places_in_pred
                    .iter()
                    .map(|p| {
                        self.state
                            .acc()
                            .iter()
                            .chain(self.state.pred().iter())
                            .filter(|(place, _)| place.has_prefix(p.get_place()))
                            .map(|(place, perm_amount)| {
                                trace!("Place {} can offer {}", place, perm_amount);
                                *perm_amount
                            })
                            .min()
                            .unwrap_or(PermAmount::Write)
                    })
                    .min()
                    .unwrap_or(PermAmount::Write);
                trace!(
                    "We want to fold {} with permission {} (we need at least {})",
                    req,
                    perm_amount,
                    req.get_perm_amount()
                );

                for fold_req_place in &places_in_pred {
                    let pos = req.get_place().pos();
                    let new_req_place = fold_req_place.clone().set_default_pos(pos);
                    let obtain_result = self.obtain(&new_req_place, false)?;
                    match obtain_result {
                        ObtainResult::Success(new_actions) => {
                            actions.extend(new_actions);
                        }
                        ObtainResult::Failure(_) => {
                            return Ok(obtain_result);
                        }
                    }
                }

                let scaled_places_in_pred: Vec<_> = places_in_pred
                    .into_iter()
                    .map(|perm| perm.update_perm_amount(perm_amount))
                    .collect();

                let pos = req.get_place().pos();
                let fold_action = Action::Fold(vir::Fold {
                    predicate_name: predicate_name.clone(),
                    arguments: vec![req.get_place().clone()],
                    permission: perm_amount,
                    enum_variant: variant,
                    position: pos,
                });
                actions.push(fold_action);

                // Simulate folding of `req`
                debug_assert!(self.state.contains_all_perms(scaled_places_in_pred.iter()));
                debug_assert!(
                    !req.get_place().is_simple_place() || self.state.contains_acc(req.get_place()),
                    "req={} state={}",
                    req.get_place(),
                    self.state
                );
                debug_assert!(!self.state.contains_pred(req.get_place()));
                self.state.remove_all_perms(scaled_places_in_pred.iter())?;
                self.state
                    .insert_pred(req.get_place().clone(), perm_amount)?;

                // Done. Continue checking the remaining requirements
                trace!("We folded {}", req);
                trace!("[exit] obtain");
                Ok(ObtainResult::Success(actions))
            } else {
                debug!(
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
                Ok(ObtainResult::Failure(req.clone()))
            }
        } else if in_join && req.get_perm_amount() == PermAmount::Read {
            // Permissions held by shared references can be dropped
            // without being explicitly moved because &T implements Copy.
            Ok(ObtainResult::Failure(req.clone()))
        } else {
            // We have no predicate to obtain the access permission `req`
            debug!(
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
            Ok(ObtainResult::Failure(req.clone()))
        }
    }

    /// Returns some of the dropped permissions
    pub fn apply_stmt(&mut self, stmt: &vir::Stmt) -> Result<(), FoldUnfoldError> {
        trace!("apply_stmt: {}", stmt);

        trace!("Acc state before: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state before: {{\n{}\n}}", self.state.display_pred());

        self.state.check_consistency();

        stmt.apply_on_state(&mut self.state, self.predicates)?;

        trace!("Acc state after: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state after: {{\n{}\n}}", self.state.display_pred());

        self.state.check_consistency();

        Ok(())
    }

    pub fn obtain_permissions(
        &mut self,
        permissions: Vec<Perm>,
    ) -> Result<Vec<Action>, FoldUnfoldError> {
        trace!(
            "[enter] obtain_permissions: {}",
            permissions.iter().to_string()
        );

        // Solve conflicting requirements
        // See issue https://github.com/viperproject/prusti-dev/issues/362
        let permissions = solve_conficts(permissions);
        trace!(
            "After solving conflicts: {}",
            permissions.iter().to_string()
        );

        trace!("Acc state before: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state before: {{\n{}\n}}", self.state.display_pred());

        self.state.check_consistency();

        let actions = self.obtain_all(permissions)?;

        trace!("Acc state after: {{\n{}\n}}", self.state.display_acc());
        trace!("Pred state after: {{\n{}\n}}", self.state.display_pred());

        self.state.check_consistency();

        trace!("[exit] obtain_permissions: {}", actions.iter().to_string());
        Ok(actions)
    }
}

/// Find in `variant_place` the variant index of the enum encoded by `enum_place`.
fn find_variant(enum_place: &vir::Expr, variant_place: &vir::Expr) -> vir::MaybeEnumVariantIndex {
    trace!(
        "[enter] find_variant(enum_place={}, variant_place={})",
        enum_place,
        variant_place
    );
    let parent = variant_place.get_parent_ref().unwrap();
    let result = if enum_place == parent {
        match variant_place {
            vir::Expr::Variant(vir::Variant { variant_index, .. }) => Some(variant_index.into()),
            _ => None,
        }
    } else {
        find_variant(enum_place, parent)
    };
    trace!(
        "[exit] find_variant(place={}, variant_place={}) = {:?}",
        enum_place,
        variant_place,
        result
    );
    result
}

/// Find the variant of the place encoding an expression.
/// Note: the place needs to be unfolded and downcasted for this to work.
pub fn find_unfolded_variant(state: &State, enum_place: &vir::Expr) -> vir::MaybeEnumVariantIndex {
    debug_assert!(enum_place.is_place());
    // Find an access permission for which req is a proper suffix and extract variant from it.
    let variants: HashSet<_> = state
        .acc_places()
        .into_iter()
        .filter(|place| place.has_proper_prefix(enum_place) && place.is_variant())
        .flat_map(|variant_place| find_variant(enum_place, &variant_place))
        .collect();
    debug_assert!(variants.len() <= 1);
    variants.into_iter().next()
}

/// Computes a pair of sets of places that should be obtained. The first
/// element of the pair is the set of places that should be obtained by
/// unfolding while the second element should be obtained by folding.
///
/// The first set is computed by taking the elements that have a prefix
/// in another set. For example:
///
/// ```plain
///   { a, b.c, d.e.f, d.g },
///   { a, b.c.d, b.c.e, d.e,h }
/// ```
///
/// becomes:
///
/// ```plain
/// { a, b.c.d, b.c.e, d.e.f }
/// ```
///
/// The second set is the set of enums that are unfolded differently in
/// input sets.
///
/// The elements from the first set that have any element in the second
/// set as a prefix are dropped.
pub fn compute_fold_target(
    left: &HashSet<vir::Expr>,
    right: &HashSet<vir::Expr>,
) -> (HashSet<vir::Expr>, HashSet<vir::Expr>) {
    let mut conflicting_base = HashSet::new();
    // If we have an enum unfolded only in one, then we add that enum to
    // conflicting places.
    let mut conflicting_base_check = |item: &vir::Expr, second_set: &HashSet<vir::Expr>| {
        if let vir::Expr::Variant(vir::Variant { box ref base, .. }) = item {
            if !second_set.iter().any(|p| p.has_prefix(item)) {
                // The enum corresponding to base is completely folded in second_set or unfolded
                // with a different variant.
                conflicting_base.insert(base.clone());
            }
        }
    };
    for left_item in left.iter() {
        conflicting_base_check(left_item, right);
    }
    for right_item in right.iter() {
        conflicting_base_check(right_item, left);
    }

    let mut places = HashSet::new();
    let mut place_check =
        |item: &vir::Expr, item_set: &HashSet<vir::Expr>, other_set: &HashSet<vir::Expr>| {
            let is_leaf = !item_set.iter().any(|p| p.has_proper_prefix(item));
            let below_all_others = !other_set.iter().any(|p| p.has_prefix(item));
            let no_conflict_base = !conflicting_base.iter().any(|base| item.has_prefix(base));
            if is_leaf && below_all_others && no_conflict_base {
                places.insert(item.clone());
            }
        };
    for left_item in left.iter() {
        place_check(left_item, left, right);
    }
    for right_item in right.iter() {
        place_check(right_item, right, left);
    }

    let acc_places = places;
    let pred_places: HashSet<_> = conflicting_base
        .iter()
        .filter(|place| {
            !conflicting_base
                .iter()
                .any(|base| place.has_proper_prefix(base))
        })
        .cloned()
        .collect();
    (acc_places, pred_places)
}

/// Solve conflicting requirements.
///
/// Example:
/// * Conflicting requirements: `P(x.f) && P(x.f.g) && acc(x.f.g)`
/// * Solution: `P(x.f)`
/// * Explanation: `P(x.f.g)` and `acc(x.f.g)` can be obtained with an unfolding expression,
///   which is always allowed.
///
/// See also: issue https://github.com/viperproject/prusti-dev/issues/362
fn solve_conficts(perms: Vec<Perm>) -> Vec<Perm> {
    // TODO: the time complexity is quadratic, but it can be improved (as many other functions
    //   used in fold-unfold) by building and using the prefix tree of a set of `Perm`.
    perms
        .iter()
        .filter(|p| {
            let p_place = p.get_place();
            !perms
                .iter()
                .any(|q| q.is_pred() && p_place.has_proper_prefix(q.get_place()))
        })
        .cloned()
        .collect()
}

/// Result of the obtain operation. Either success and a list of actions, or failure and the
/// permission that was missing.
enum ObtainResult {
    Success(Vec<Action>),
    Failure(Perm),
}

impl ObtainResult {
    pub fn get_actions(self) -> Result<Vec<Action>, FoldUnfoldError> {
        match self {
            ObtainResult::Success(actions) => Ok(actions),
            ObtainResult::Failure(p) => Err(FailedToObtain(p)),
        }
    }
}
