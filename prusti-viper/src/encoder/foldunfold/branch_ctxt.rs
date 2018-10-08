// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::foldunfold::permissions::*;
use encoder::foldunfold::state::*;
use encoder::foldunfold::action::*;
use encoder::vir;
use encoder::vir::Frac;
use encoder::vir::{Zero, One};
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use encoder::foldunfold::places_utils::*;
use encoder::foldunfold::perm::LabelledPermIterator;
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
                HashMap::from_iter(local_vars.into_iter().map(|v| (vir::Place::Base(v), Frac::one()))),
                HashMap::new(),
                HashSet::new(),
                HashSet::new()
            ),
            predicates
        }
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
    fn unfold(&mut self, pred_place: &vir::Place, frac: Frac) -> Action {
        debug!("We want to unfold {:?}", pred_place);
        assert!(self.state.contains_acc(&pred_place));
        assert!(self.state.contains_pred(&pred_place));

        let predicate_name = pred_place.typed_ref_name().unwrap();
        let predicate = self.predicates.get(&predicate_name).unwrap();

        let pred_self_place: vir::Place = predicate.args[0].clone().into();
        let places_in_pred: Vec<Perm> = predicate.get_permissions().into_iter()
            .map(
                |perm| {
                    perm.map_place( |p|
                        p.replace_prefix(&pred_self_place, pred_place.clone())
                    ) * frac
                }
            ).collect();

        trace!("Pred state before unfold: {{{}}}", self.state.display_debug_pred());

        // Simulate unfolding of `pred_place`
        self.state.remove_pred(&pred_place, frac);
        self.state.insert_all_perms(places_in_pred.into_iter());

        debug!("We unfolded {:?}", pred_place);

        trace!("Pred state after unfold: {{{}}}", self.state.display_debug_pred());

        Action::Unfold(predicate_name.clone(), vec![ pred_place.clone().into() ], frac)
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
            let moved_paths: HashSet<_> = ancestors(
                &self.state.moved().clone().union(other.state.moved()).cloned().collect()
            );
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
                if !self.state.acc().contains_key(acc_place) {
                    debug!("The left branch needs to obtain an access permission: {}", acc_place);
                    let frac = other.state.acc()[acc_place];
                    // Unfold something and get `acc_place`
                    left_actions.extend(
                        self.obtain(&Perm::Acc(acc_place.clone(), frac))
                    );
                }
                if !other.state.acc().contains_key(acc_place) {
                    debug!("The right branch needs to obtain an access permission: {}", acc_place);
                    let frac = self.state.acc()[acc_place];
                    // Unfold something and get `acc_place`
                    right_actions.extend(
                        other.obtain(&Perm::Acc(acc_place.clone(), frac))
                    );
                }
            }

            // Drop predicate permissions that can not be obtained due to a move
            for pred_place in &filter_proper_extensions_of(&self.state.pred_places(), &moved_paths) {
                debug!("Drop pred {} in left branch (it is moved out in the other branch)", pred_place);
                assert!(self.state.pred().contains_key(&pred_place));
                let frac = self.state.remove_pred_place(&pred_place);
                left_actions.push(
                    Action::Drop(Perm::Pred(pred_place.clone(), frac))
                );
            }
            for pred_place in &filter_proper_extensions_of(&other.state.pred_places(), &moved_paths) {
                debug!("Drop pred {} in right branch (it is moved out in the other branch)", pred_place);
                assert!(other.state.pred().contains_key(&pred_place));
                let frac = other.state.remove_pred_place(&pred_place);
                right_actions.push(
                    Action::Drop(Perm::Pred(pred_place.clone(), frac))
                );
            }

            // Compute preserved predicate permissions
            let preserved_preds: HashSet<_> = intersection(&self.state.pred_places(), &other.state.pred_places());
            debug!("preserved_preds: {:?}", preserved_preds);

            // Drop predicate permissions that are not in the other branch
            for pred_place in self.state.pred_places().difference(&preserved_preds) {
                debug!("Drop pred {} in left branch (it is not in the other branch)", pred_place);
                assert!(self.state.pred().contains_key(&pred_place));
                let frac = self.state.remove_pred_place(&pred_place);
                left_actions.push(
                    Action::Drop(Perm::Pred(pred_place.clone(), frac))
                );
            }
            for pred_place in other.state.pred_places().difference(&preserved_preds) {
                debug!("Drop pred {} in right branch (it is not in the other branch)", pred_place);
                assert!(other.state.pred().contains_key(&pred_place));
                let frac = other.state.remove_pred_place(&pred_place);
                right_actions.push(
                    Action::Drop(Perm::Pred(pred_place.clone(), frac))
                );
            }

            // Drop access permissions that can not be obtained due to a move
            for acc_place in &filter_proper_extensions_of(&self.state.acc_places(), &moved_paths) {
                debug!("Drop acc {} in left branch (it is moved out in the other branch)", acc_place);
                assert!(self.state.acc().contains_key(&acc_place));
                let frac = self.state.remove_acc_place(&acc_place);
                left_actions.push(
                    Action::Drop(Perm::Acc(acc_place.clone(), frac))
                );
            }
            for acc_place in &filter_proper_extensions_of(&other.state.acc_places(), &moved_paths) {
                debug!("Drop acc {} in right branch (it is moved out in the other branch)", acc_place);
                assert!(other.state.acc().contains_key(&acc_place));
                let frac = other.state.remove_acc_place(&acc_place);
                right_actions.push(
                    Action::Drop(Perm::Acc(acc_place.clone(), frac))
                );
            }

            trace!("Actions in left branch: {:?}", &left_actions);
            trace!("Actions in left branch: {:?}", &right_actions);

            assert_eq!(self.state.acc(), other.state.acc());
            assert_eq!(self.state.pred(), other.state.pred());
            self.state.check_consistency();
        }

        return (left_actions, right_actions);
    }

    /// Obtain the required permissions, changing the state inplace and returning the statements.
    fn obtain_all(&mut self, reqs: Vec<Perm>) -> Vec<Action> {
        debug!("Obtain all: {{{}}}", reqs.iter().to_string());
        reqs.iter()
            .flat_map(|perm| self.obtain(perm))
            .collect()
    }

    /// Obtain the required permission, changing the state inplace and returning the statements.
    fn obtain(&mut self, req: &Perm) -> Vec<Action> {
        debug!("Obtain: {}", req);

        let mut actions: Vec<Action> = vec![];

        trace!("Acc state: {{{}}}", self.state.display_debug_acc());
        trace!("Pred state: {{{}}}", self.state.display_debug_pred());

        let req_place = req.get_place();

        // 1. Check if the requirement is satisfied
        if self.state.contains_perm(req) {
            // `req` is satisfied, so we can remove it from `reqs`
            debug!("Requirement {} is satisfied", req);
            return actions;
        }
        if let Perm::Acc(vir::Place::Base(_), _frac) = req {
            // access permissions on local variables are always satisfied
            debug!("Requirement {} is satisfied", req);
            return actions;
        }

        debug!("Try to satisfy requirement {:?}", req);

        // 2. Obtain by restoring a borrowed path with a magic wand
        let existing_prefix_borrowed_opt: Option<vir::Place> = self.state.borrowed().iter()
            .find(|p| req_place.has_prefix(p))
            .cloned();
        if let Some(existing_borrowed_to_restore) = existing_prefix_borrowed_opt {
            debug!("We want to restore {:?}", existing_borrowed_to_restore);
            let action = unimplemented!();
            actions.push(action);
            debug!("We restored {:?}", existing_borrowed_to_restore);

            // Check if we are done
            actions.extend(self.obtain(req));
            return actions;
        }

        // 3. Obtain with an unfold
        // Find a predicate on a proper prefix of req_place
        let existing_prefix_pred_opt: Option<vir::Place> = self.state.pred_places().iter()
            .find(|p| req_place.has_proper_prefix(p))
            .cloned();
        if let Some(existing_pred_to_unfold) = existing_prefix_pred_opt {
            let frac = self.state.pred()[&existing_pred_to_unfold];
            debug!("We want to unfold {:?} with permission {} (we need at least {})", existing_pred_to_unfold, frac, req.get_frac());
            assert!(frac >= req.get_frac());
            let action = self.unfold(&existing_pred_to_unfold, frac);
            actions.push(action);
            debug!("We unfolded {:?}", existing_pred_to_unfold);

            // Check if we are done
            actions.extend(self.obtain(req));
            return actions;
        }

        // 4. Obtain with a fold
        if let Perm::Pred(_, _) = req {
            // We want to fold `req_place`
            debug!("We want to fold {:?}", req_place);
            let predicate_name = req_place.typed_ref_name().unwrap();
            let predicate = self.predicates.get(&predicate_name).unwrap();

            let pred_self_place: vir::Place = predicate.args[0].clone().into();
            let places_in_pred: Vec<Perm> = predicate.get_permissions().into_iter()
                .map(
                    |perm| {
                        perm.map_place( |p|
                            p.replace_prefix(&pred_self_place, req_place.clone())
                        )
                    }
                ).collect();

            // Find an access permission for which req_place is a proper suffix
            let existing_proper_perm_extension_opt: Option<_> = self.state.acc_places().into_iter().find(
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
                    actions.extend(self.obtain(fold_req_place));
                }

                // We want to fold using the maximum possible fraction
                let frac = places_in_pred.iter().map(|p| self.state.get_available_frac(p)).min().unwrap_or(Frac::one());
                debug!("We want to fold {:?} with permission {} (we need at least {})", req_place, frac, req.get_frac());
                assert!(frac >= req.get_frac());

                let scaled_places_in_pred: Vec<Perm> = places_in_pred.into_iter().map(|p| p * frac).collect();

                actions.push(
                    Action::Fold(predicate_name.clone(), vec![ req_place.clone().into() ], frac)
                );

                // Simulate folding of `req_place`
                assert!(self.state.contains_all_perms(scaled_places_in_pred.iter()));
                assert!(self.state.contains_acc(&req_place));
                assert!(!self.state.contains_pred(&req_place));
                self.state.remove_all_perms(scaled_places_in_pred.iter());
                self.state.insert_pred(req_place.clone(), frac);

                // Done. Continue checking the remaining requirements
                debug!("We folded {:?}", req_place);
                return actions;
            }
        } else {
            // We have no predicate to obtain the access permission `req`
            unreachable!(
                "There is no predicate to obtain {}: {}. Predicates: {:?}",
                req.place_as_ref(),
                req.place_as_ref().get_type(),
                self.state.pred()
            );
        };

        unreachable!(
            "It is not possible to obtain {}: {}. Predicates: {:?}",
            req.place_as_ref(),
            req.place_as_ref().get_type(),
            self.state.pred()
        );
    }

    /// Returns some of the dropped permissions
    pub fn apply_stmt(&mut self, stmt: &vir::Stmt) -> HashSet<Perm> {
        debug!("apply_stmt: {}", stmt);

        trace!("Acc state before: {{{}}}", self.state.display_acc());
        trace!("Pred state before: {{{}}}", self.state.display_pred());

        self.state.check_consistency();

        let mut dropped_permissions = HashSet::new();
        stmt.apply_on_state(&mut self.state, self.predicates, &mut dropped_permissions);

        trace!("Dropped permissions: {{{}}}", dropped_permissions.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "));
        trace!("Acc state after: {{{}}}", self.state.display_acc());
        trace!("Pred state after: {{{}}}", self.state.display_pred());

        self.state.check_consistency();

        dropped_permissions
    }

    pub fn obtain_permissions(&mut self, permissions: Vec<Perm>) -> Vec<Action> {
        debug!("obtain_permissions: {}", permissions.iter().to_string());

        trace!("Acc state before: {{{}}}", self.state.display_acc());
        trace!("Pred state before: {{{}}}", self.state.display_pred());

        self.state.check_consistency();

        let actions = self.obtain_all(permissions);

        trace!("Acc state after: {{{}}}", self.state.display_acc());
        trace!("Pred state after: {{{}}}", self.state.display_pred());

        self.state.check_consistency();

        actions
    }
}
