// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::foldunfold::perm::*;
use crate::encoder::foldunfold::permissions::*;
use crate::encoder::foldunfold::state::*;
use prusti_common::vir;
use std::collections::HashMap;
use log::{debug, trace};

fn inhale_expr(expr: &vir::Expr, state: &mut State, predicates: &HashMap<String, vir::Predicate>) {
    state.insert_all_perms(
        expr.get_permissions(predicates)
            .into_iter()
            .filter(|p| !(p.is_local() && p.is_acc())),
    );
}

fn exhale_expr(expr: &vir::Expr, state: &mut State, predicates: &HashMap<String, vir::Predicate>) {
    state.remove_all_perms(
        expr.get_permissions(predicates)
            .iter()
            .filter(|p| p.is_curr() || p.is_pred())
            .filter(|p| !(p.is_local() && p.is_acc()))
            // Hack for final exhale of method: do not remove "old[pre](..)" permissions from state
            .filter(|p| p.get_label() != Some(&"pre".to_string())),
    );
}

pub trait ApplyOnState {
    fn apply_on_state(&self, state: &mut State, predicates: &HashMap<String, vir::Predicate>);
}

impl ApplyOnState for vir::Stmt {
    fn apply_on_state(&self, state: &mut State, predicates: &HashMap<String, vir::Predicate>) {
        debug!("apply_on_state '{}'", self);
        trace!("State acc before {{\n{}\n}}", state.display_acc());
        trace!("State pred before {{\n{}\n}}", state.display_pred());
        trace!("State moved before {{\n{}\n}}", state.display_moved());
        match self {
            &vir::Stmt::Comment(_)
            | &vir::Stmt::Label(_)
            | &vir::Stmt::Assert(_, _, _)
            | &vir::Stmt::Obtain(_, _) => {}

            &vir::Stmt::Inhale(ref expr, _) => {
                inhale_expr(expr, state, predicates);
            }

            &vir::Stmt::Exhale(ref expr, _) => {
                exhale_expr(expr, state, predicates);
            }

            &vir::Stmt::MethodCall(_, _, ref targets) => {
                // We know that in Prusti method's preconditions and postconditions are empty
                state.remove_moved_matching(|p| targets.contains(&p.get_base()));
                state.remove_pred_matching(|p| p.is_curr() && targets.contains(&p.get_base()));
                state.remove_acc_matching(|p| {
                    p.is_curr() && !p.is_local() && targets.contains(&p.get_base())
                });
            }

            &vir::Stmt::Assign(ref lhs_place, ref rhs, kind) if kind != vir::AssignKind::Ghost => {
                debug_assert!(lhs_place.is_place());
                let original_state = state.clone();

                // Check the state of rhs.
                if kind != vir::AssignKind::Copy {
                    assert!(rhs.is_place());
                    assert!(rhs.get_type().is_ref());

                    // Check that the rhs contains no moved paths
                    assert!(
                        !state.is_prefix_of_some_moved(&rhs),
                        "The rhs place of statement '{}' is currently moved-out or blocked due to a borrow",
                        self
                    );
                    for prefix in rhs.all_proper_prefixes() {
                        assert!(!state.contains_pred(&prefix));
                    }
                }

                // Remove places that will not have a name
                state.remove_moved_matching(|p| p.has_prefix(&lhs_place));
                state.remove_pred_matching(|p| p.has_prefix(&lhs_place));
                state.remove_acc_matching(|p| p.has_proper_prefix(&lhs_place));

                // In case of move or borrowing, move permissions from the `rhs` to the `lhs`
                if rhs.is_place() && rhs.get_type().is_ref() {
                    // This is a move assignemnt or the creation of a borrow
                    match kind {
                        vir::AssignKind::Move | vir::AssignKind::MutableBorrow(_) => {
                            // In Prusti, we lose permission on the rhs
                            state.remove_pred_matching(|p| p.has_prefix(&rhs));
                            state.remove_acc_matching(|p| {
                                p.has_proper_prefix(&rhs) && !p.is_local()
                            });

                            // We also lose permission on the lhs
                            state.remove_pred_matching(|p| p.has_prefix(&lhs_place));
                            state.remove_acc_matching(|p| {
                                p.has_proper_prefix(&lhs_place) && !p.is_local()
                            });

                            // And we create permissions for the lhs
                            let new_acc_places = original_state
                                .acc()
                                .iter()
                                .filter(|(p, _)| p.has_proper_prefix(&rhs))
                                .map(|(p, perm_amount)| {
                                    (p.clone().replace_place(&rhs, lhs_place), *perm_amount)
                                })
                                .filter(|(p, _)| !p.is_local());
                            state.insert_all_acc(new_acc_places);

                            let new_pred_places = original_state
                                .pred()
                                .iter()
                                .filter(|(p, _)| p.has_prefix(&rhs))
                                .map(|(p, perm_amount)| {
                                    (p.clone().replace_place(&rhs, lhs_place), *perm_amount)
                                });
                            state.insert_all_pred(new_pred_places);

                            // Finally, mark the rhs as moved
                            if !rhs.has_prefix(lhs_place) {
                                state.insert_moved(rhs.clone());
                            }
                        }
                        vir::AssignKind::SharedBorrow(_) => {
                            // We lose permission on the lhs
                            state.remove_pred_matching(|p| p.has_prefix(&lhs_place));
                            state.remove_acc_matching(|p| {
                                p.has_proper_prefix(&lhs_place) && !p.is_local()
                            });
                        }
                        vir::AssignKind::Ghost | vir::AssignKind::Copy => {
                            unreachable!();
                        }
                    }
                } else {
                    // This is not move assignemnt or the creation of a borrow
                    assert!(
                        match kind {
                            vir::AssignKind::Copy => true,
                            _ => false,
                        },
                        "Unexpected assignment kind: {:?}",
                        kind
                    );
                }
            }

            &vir::Stmt::Assign(ref _lhs_place, ref _rhs, vir::AssignKind::Ghost) => {
                // Do nothing.
            }

            &vir::Stmt::Fold(ref _pred_name, ref args, perm_amount, ref variant, _) => {
                assert_eq!(args.len(), 1);
                let place = &args[0];
                debug_assert!(place.is_place());
                assert!(!state.contains_pred(place));
                assert!(!state.is_prefix_of_some_moved(place));

                // We want to fold place
                let predicate_name = place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Expr = predicate.self_place();
                let places_in_pred: Vec<Perm> = predicate
                    .get_permissions_with_variant(variant)
                    .into_iter()
                    .map(|perm| {
                        perm.map_place(|p| p.replace_place(&pred_self_place, place))
                            .init_perm_amount(perm_amount)
                    })
                    .collect();

                // Commented due to the presence of implications in the body of predicates
                //for contained_place in &places_in_pred {
                //    assert!(state.contains(contained_place));
                //}

                // Simulate folding of `place`
                state.remove_all_perms(places_in_pred.iter());
                state.insert_pred(place.clone(), perm_amount);
            }

            &vir::Stmt::Unfold(ref _pred_name, ref args, perm_amount, ref variant) => {
                assert_eq!(args.len(), 1);
                let place = &args[0];
                debug_assert!(place.is_place());
                assert!(state.contains_pred(place));
                assert!(!state.is_prefix_of_some_moved(place));

                // We want to unfold place
                let predicate_name = place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Expr = predicate.self_place();
                let places_in_pred: Vec<_> = predicate
                    .get_permissions_with_variant(variant)
                    .into_iter()
                    .map(|aop| aop.map_place(|p| p.replace_place(&pred_self_place, place)))
                    .collect();

                for contained_place in &places_in_pred {
                    assert!(!state.contains_perm(contained_place));
                }

                // Simulate unfolding of `place`
                state.remove_pred(place, perm_amount);
                state.insert_all_perms(places_in_pred.into_iter());
            }

            &vir::Stmt::BeginFrame => state.begin_frame(),

            &vir::Stmt::EndFrame => state.end_frame(),

            &vir::Stmt::TransferPerm(ref lhs_place, ref rhs_place, unchecked) => {
                let original_state = state.clone();

                debug_assert!(
                    !lhs_place.is_simple_place() || state.is_prefix_of_some_acc(lhs_place) || state.is_prefix_of_some_pred(lhs_place),
                    "The fold/unfold state does not contain the permission for an expiring borrow: {}",
                    lhs_place
                );
                /*assert!(
                    state.is_prefix_of_some_pred(lhs_place),
                    "The fold/unfold state does not contain the permission for an expiring borrow: {}",
                    lhs_place
                );*/
                debug_assert!(lhs_place.get_type().is_ref());
                debug_assert!(rhs_place.get_type().is_ref());
                debug_assert_eq!(lhs_place.get_type(), rhs_place.get_type());
                //debug_assert!(!state.is_proper_prefix_of_some_acc(rhs_place));
                //debug_assert!(!state.is_prefix_of_some_pred(rhs_place));
                //debug_assert!(!lhs_place.is_curr() || !state.is_prefix_of_some_moved(lhs_place));

                // Restore permissions from the `lhs` to the `rhs`

                // In Prusti, lose permission from the lhs and rhs
                state.remove_pred_matching(|p| p.has_prefix(&lhs_place));
                state.remove_acc_matching(|p| p.has_proper_prefix(&lhs_place) && !p.is_local());
                state.remove_pred_matching(|p| p.has_prefix(&rhs_place));
                state.remove_acc_matching(|p| p.has_proper_prefix(&rhs_place) && !p.is_local());

                // The rhs is no longer moved
                state.remove_moved_matching(|p| p.has_prefix(rhs_place));

                // And we create permissions for the rhs
                let new_acc_places: Vec<_> = original_state
                    .acc()
                    .iter()
                    .filter(|(p, _)| p.has_proper_prefix(lhs_place))
                    .map(|(p, perm_amount)| {
                        (p.clone().replace_place(&lhs_place, rhs_place), *perm_amount)
                    })
                    .filter(|(p, _)| !p.is_local())
                    .collect();

                let new_pred_places: Vec<_> = original_state
                    .pred()
                    .iter()
                    .filter(|(p, _)| p.has_prefix(lhs_place))
                    .map(|(p, perm_amount)| {
                        (p.clone().replace_place(&lhs_place, rhs_place), *perm_amount)
                    })
                    .collect();

                assert!(
                    (lhs_place == lhs_place) || !(new_acc_places.is_empty() && new_pred_places.is_empty()),
                    "Statement '{}' restored not permissions in state with acc {{\n{}\n}}\nand pred {{\n{}\n}}",
                    self,
                    original_state.display_acc(),
                    original_state.display_pred()
                );

                state.insert_all_acc(new_acc_places.into_iter());
                state.insert_all_pred(new_pred_places.into_iter());

                // Move also the acc permission if the rhs is old.
                if state.contains_acc(lhs_place) && !state.contains_acc(rhs_place) {
                    if rhs_place.is_old() {
                        debug!("Moving acc({}) to acc({}) state.", lhs_place, rhs_place);
                        state.insert_acc(
                            rhs_place.clone(),
                            state.acc().get(lhs_place).unwrap().clone(),
                        );
                        if !lhs_place.is_local() && !lhs_place.is_curr() {
                            state.remove_acc_place(lhs_place);
                        }
                    }
                }

                // Remove the lhs access permission if it was old.
                if state.contains_acc(lhs_place) && lhs_place.is_old() {
                    state.remove_acc_place(lhs_place);
                }

                /*
                // Hack: Move also the acc permission
                if state.contains_acc(lhs_place) && !state.contains_acc(rhs_place) {
                    debug!("Moving acc({}) to acc({}) state.", lhs_place, rhs_place);
                    state.insert_acc(
                        rhs_place.clone(),
                        state.acc().get(lhs_place).unwrap().clone()
                    );
                    if !lhs_place.is_local() && lhs_place.is_curr() {
                        state.remove_acc_place(lhs_place);
                    }
                }
                */

                // Finally, mark the lhs as moved
                if !lhs_place.has_prefix(rhs_place) &&   // Maybe this is always true?
                        !unchecked
                {
                    state.insert_moved(lhs_place.clone());
                }
            }

            &vir::Stmt::PackageMagicWand(
                vir::Expr::MagicWand(ref lhs, ref rhs, _, _),
                ref _stmts,
                ref _label,
                ref _vars,
                ref _pos,
            ) => {
                // The semantics of the statements is handled in `foldunfold/mod.rs`.
                //for stmt in package_stmts {
                //    stmt.apply_on_state(state, predicates);
                //}
                exhale_expr(rhs, state, predicates);
                inhale_expr(lhs, state, predicates);
            }

            &vir::Stmt::ApplyMagicWand(vir::Expr::MagicWand(ref lhs, ref rhs, _, _), _) => {
                exhale_expr(lhs, state, predicates);
                inhale_expr(rhs, state, predicates);
            }

            &vir::Stmt::ExpireBorrows(ref _dag) => {
                // TODO: #133
            }

            ref x => unimplemented!("{}", x),
        }
    }
}
