// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// TODO: Remove this and fix.
#![allow(deprecated)]

use encoder::foldunfold::perm::*;
use encoder::foldunfold::state::*;
use encoder::vir;
use std::collections::HashMap;
use std::collections::HashSet;

fn inhale_expr(expr: &vir::Expr, state: &mut State, predicates: &HashMap<String, vir::Predicate>) {
    state.insert_all_perms(
        expr.get_permissions(predicates).into_iter()
            .filter(|p| !(p.is_base() && p.is_acc()))
    );
}

fn exhale_expr(expr: &vir::Expr, state: &mut State, predicates: &HashMap<String, vir::Predicate>) {
    state.remove_all_perms(
        expr.get_permissions(predicates).iter()
            .filter(|p| !(p.is_base() && p.is_acc()))
            // Hack for final exhale of method: do not remove "old[pre](..)" permissions from state
            .filter(|p| p.get_label() != Some(&"pre".to_string()))
    );
}

impl vir::Stmt {
    pub fn apply_on_state(&self, state: &mut State, predicates: &HashMap<String, vir::Predicate>) {
        debug!("apply_on_state '{}'", self);
        trace!("State acc before {{{}}}", state.display_acc());
        trace!("State pred before {{{}}}", state.display_pred());
        trace!("State moved before {{{}}}", state.display_moved());
        match self {
            &vir::Stmt::Comment(_) |
            &vir::Stmt::Label(_) |
            &vir::Stmt::Assert(_, _) |
            &vir::Stmt::Obtain(_) |
            &vir::Stmt::WeakObtain(_) => {}

            &vir::Stmt::Inhale(ref expr) => {
                inhale_expr(expr, state, predicates);
            }

            &vir::Stmt::Exhale(ref expr, _) => {
                exhale_expr(expr, state, predicates);
            }

            &vir::Stmt::MethodCall(_, _, ref targets) => {
                // We know that in Prusti method's preconditions and postconditions are empty
                state.remove_moved_matching(|p| targets.contains(p.get_base()));
                state.remove_pred_matching(|p| p.is_curr() && targets.contains(p.get_base()));
                state.remove_acc_matching(|p| p.is_curr() && !p.is_base() && targets.contains(p.get_base()));
            }

            &vir::Stmt::Assign(ref lhs_place, ref rhs, kind) => {
                let original_state = state.clone();

                // Mark the `rhs` as moved or borrowed
                match kind {
                    vir::AssignKind::Move => {
                        if let &vir::Expr::Place(ref rhs_place) = rhs {
                            assert!(rhs_place.get_type().is_ref());

                            // Check that the rhs contains no moved paths
                            assert!(!state.is_prefix_of_some_moved(&rhs_place));
                            for prefix in rhs_place.all_proper_prefixes() {
                                assert!(!state.contains_pred(prefix));
                            }

                            state.insert_moved(rhs_place.clone());
                        } else {
                            unreachable!()
                        }
                    }
                    vir::AssignKind::MutableBorrow => {
                        if let &vir::Expr::Place(ref rhs_place) = rhs {
                            assert!(rhs_place.get_type().is_ref());

                            // Check that the rhs contains no moved paths
                            assert!(!state.is_prefix_of_some_moved(&rhs_place));
                            for prefix in rhs_place.all_proper_prefixes() {
                                assert!(!state.contains_pred(prefix));
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    _ => {}
                }

                // Remove places that will not have a name
                state.remove_moved_matching(|p| p.has_prefix(&lhs_place));
                state.remove_pred_matching(|p| p.has_prefix(&lhs_place));
                state.remove_acc_matching(|p| p.has_proper_prefix(&lhs_place));

                // In case of move or borrowing, move permissions from the `rhs` to the `lhs`
                match rhs {
                    &vir::Expr::Place(ref rhs_place) if rhs_place.get_type().is_ref() => {
                        // This is a move assignemnt or the creation of a mutable borrow
                        assert!(match kind { vir::AssignKind::Copy => false, _ => true }, "Unexpected assignment kind: {:?}", kind);

                        // In Prusti, we lose permission on the rhs
                        state.remove_pred_matching( |p| p.has_prefix(&rhs_place));
                        state.remove_acc_matching( |p| p.has_proper_prefix(&rhs_place) && !p.is_base());

                        // We also lose permission on the lhs
                        state.remove_pred_matching( |p| p.has_prefix(&lhs_place));
                        state.remove_acc_matching( |p| p.has_proper_prefix(&lhs_place) && !p.is_base());

                        // And we create permissions for the lhs
                        let new_acc_places = original_state.acc().iter()
                            .filter(|(p, _)| p.has_proper_prefix(&rhs_place))
                            .map(|(p, frac)| (p.clone().replace_prefix(&rhs_place, lhs_place.clone()), *frac))
                            .filter(|(p, _)| !p.is_base());
                        state.insert_all_acc(new_acc_places);

                        let new_pred_places = original_state.pred().iter()
                            .filter(|(p, _)| p.has_prefix(&rhs_place))
                            .map(|(p, frac)| (p.clone().replace_prefix(&rhs_place, lhs_place.clone()), *frac));
                        state.insert_all_pred(new_pred_places);
                    }
                    _ => {
                        // This is not move assignemnt or the creation of a mutable borrow
                        assert!(match kind { vir::AssignKind::Copy => true, _ => false }, "Unexpected assignment kind: {:?}", kind);
                    }
                }
            }

            &vir::Stmt::Fold(ref pred_name, ref args, frac) => {
                assert_eq!(args.len(), 1);
                let place = &args[0].clone().as_place().unwrap();
                assert!(!state.contains_pred(place));
                assert!(!state.is_prefix_of_some_moved(place));

                // We want to fold place
                let predicate_name = place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: Vec<Perm> = predicate.get_permissions().into_iter()
                    .map(
                        |perm| {
                            perm.map_place( |p|
                                p.replace_prefix(&pred_self_place, place.clone())
                            ) * frac
                        }
                    ).collect();

                // Commented due to the presence of implications in the body of predicates
                //for contained_place in &places_in_pred {
                //    assert!(state.contains(contained_place));
                //}

                // Simulate folding of `place`
                state.remove_all_perms(places_in_pred.iter());
                state.insert_pred(place.clone(), frac);
            }

            &vir::Stmt::Unfold(ref pred_name, ref args, frac) => {
                assert_eq!(args.len(), 1);
                let place = &args[0].clone().as_place().unwrap();
                assert!(state.contains_pred(place));
                assert!(!state.is_prefix_of_some_moved(place));

                // We want to unfold place
                let predicate_name = place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: Vec<_> = predicate.get_permissions().into_iter()
                    .map( |aop| aop.map_place( |p|
                        p.replace_prefix(&pred_self_place, place.clone())
                    )).collect();

                for contained_place in &places_in_pred {
                    assert!(!state.contains_perm(contained_place));
                }

                // Simulate unfolding of `place`
                state.remove_pred(place, frac);
                state.insert_all_perms(places_in_pred.into_iter());
            }

            &vir::Stmt::Havoc => {
                state.remove_acc_matching(|p| p.is_curr() && !p.is_base());
                state.remove_pred_matching(|p| p.is_curr() && !p.is_base());
                state.remove_moved_matching(|p| !p.is_base());
            }

            &vir::Stmt::BeginFrame => {
                state.begin_frame()
            }

            &vir::Stmt::EndFrame => {
                state.end_frame()
            }

            &vir::Stmt::TransferPerm(ref lhs_place, ref rhs_place) => {
                let original_state = state.clone();

                /*assert!(
                    state.is_prefix_of_some_pred(lhs_place),
                    "The fold/unfold state does not contain the permission for an expiring borrow: {}",
                    lhs_place
                );*/
                debug_assert!(lhs_place.get_type().is_ref());
                debug_assert!(rhs_place.get_type().is_ref());
                debug_assert_eq!(lhs_place.get_type(), rhs_place.get_type());
                debug_assert!(!state.is_proper_prefix_of_some_acc(rhs_place));
                debug_assert!(!state.is_prefix_of_some_pred(rhs_place));
                debug_assert!(!lhs_place.is_curr() || !state.is_prefix_of_some_moved(lhs_place));

                // Restore permissions from the `lhs` to the `rhs`

                // This is the creation of a mutable borrow

                // In Prusti, lose permission from the lhs and rhs
                state.remove_pred_matching(|p| p.has_prefix(&lhs_place));
                state.remove_acc_matching(|p| p.has_proper_prefix(&lhs_place) && !p.is_base());
                state.remove_pred_matching(|p| p.has_prefix(&rhs_place));
                state.remove_acc_matching(|p| p.has_proper_prefix(&rhs_place) && !p.is_base());

                // The rhs is no longer moved
                state.remove_moved_matching(|p| p.has_prefix(rhs_place));

                // And we create permissions for the rhs
                let new_acc_places: Vec<_> = original_state.acc().iter()
                    .filter(|(p, _)| p.has_proper_prefix(lhs_place))
                    .map(|(p, frac)| (p.clone().replace_prefix(&lhs_place, rhs_place.clone()), *frac))
                    .filter(|(p, _)| !p.is_base())
                    .collect();

                let new_pred_places: Vec<_> = original_state.pred().iter()
                    .filter(|(p, _)| p.has_prefix(lhs_place))
                    .map(|(p, frac)| (p.clone().replace_prefix(&lhs_place, rhs_place.clone()), *frac))
                    .collect();

                assert!(
                    (lhs_place == lhs_place) || !(new_acc_places.is_empty() && new_pred_places.is_empty()),
                    "Statement '{}' restored not permissions in state with:\n - acc {{{}}}\n - pred {{{}}}",
                    self,
                    original_state.display_acc(),
                    original_state.display_pred()
                );

                state.insert_all_acc(new_acc_places.into_iter());
                state.insert_all_pred(new_pred_places.into_iter());
            }

            &vir::Stmt::ExpireBorrowsIf(ref guard, ref then_stmts, ref else_stmts) => {
                unimplemented!("TODO")
            }

            &vir::Stmt::StopExpiringLoans => {
                state.remove_dropped();
            }

            &vir::Stmt::PackageMagicWand(ref lhs, ref rhs, ref package_stmts, ref _then_stmts) => {
                // TODO: we need to join this resulting state with the state that did not execute
                // the body of the package
                for stmt in package_stmts {
                    stmt.apply_on_state(state, predicates);
                }
                exhale_expr(rhs, state, predicates);
            }

            &vir::Stmt::ApplyMagicWand(ref lhs, ref rhs) => {
                exhale_expr(lhs, state, predicates);
                inhale_expr(rhs, state, predicates);
            }
        }
    }
}
