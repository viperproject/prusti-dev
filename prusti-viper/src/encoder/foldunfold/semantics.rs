// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::foldunfold::perm::*;
use crate::encoder::foldunfold::requirements::*;
use crate::encoder::foldunfold::footprint::*;
use crate::encoder::foldunfold::state::*;
use prusti_common::vir;
use std::collections::HashMap;
use log::{debug, trace};
use crate::encoder::foldunfold::FoldUnfoldError;
use crate::encoder::foldunfold::path_ctxt::find_unfolded_variant;

fn inhale_expr(expr: &vir::Expr, state: &mut State, predicates: &HashMap<String, vir::Predicate>)
    -> Result<(), FoldUnfoldError>
{
    state.insert_all_perms(
        expr.get_footprint(predicates)
            .into_iter()
            .filter(|p| !(p.is_local() && p.is_acc())),
    )
}

fn exhale_expr(expr: &vir::Expr, state: &mut State, predicates: &HashMap<String, vir::Predicate>)
    -> Result<(), FoldUnfoldError>
{
    state.remove_all_perms(
        expr.get_footprint(predicates)
            .into_iter()
            .filter(|p| p.is_curr() || p.is_pred())
            .filter(|p| !(p.is_local() && p.is_acc()))
            // Hack for final exhale of method: do not remove "old[pre](..)" permissions from state
            .filter(|p| p.get_label() != Some(&"pre".to_string())),
    )
}

pub trait ApplyOnState {
    fn apply_on_state(&self, state: &mut State, predicates: &HashMap<String, vir::Predicate>)
        -> Result<(), FoldUnfoldError>;
}

impl ApplyOnState for vir::Stmt {
    fn apply_on_state(&self, state: &mut State, predicates: &HashMap<String, vir::Predicate>)
        -> Result<(), FoldUnfoldError>
    {
        debug!("apply_on_state '{}'", self);
        trace!("State acc before {{\n{}\n}}", state.display_acc());
        trace!("State pred before {{\n{}\n}}", state.display_pred());
        trace!("State moved before {{\n{}\n}}", state.display_moved());
        match self {
            &vir::Stmt::Comment(_)
            | &vir::Stmt::Label(_)
            | &vir::Stmt::Assert(_, _)
            | &vir::Stmt::Obtain(_, _) => {}

            &vir::Stmt::Inhale(ref expr) => {
                inhale_expr(expr, state, predicates)?;
            }

            &vir::Stmt::Exhale(ref expr, _) => {
                exhale_expr(expr, state, predicates)?;
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
                    if state.is_prefix_of_some_moved(rhs) {
                        return Err(FoldUnfoldError::Unsupported("two-phase borrows are not supported".to_string()));
                    }
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
                            state.insert_all_acc(new_acc_places)?;

                            let new_pred_places = original_state
                                .pred()
                                .iter()
                                .filter(|(p, _)| p.has_prefix(&rhs))
                                .map(|(p, perm_amount)| {
                                    (p.clone().replace_place(&rhs, lhs_place), *perm_amount)
                                });
                            state.insert_all_pred(new_pred_places)?;

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
                    .get_body_footprint(variant)
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
                state.remove_all_perms(places_in_pred.iter())?;
                state.insert_pred(place.clone(), perm_amount)?;
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
                    .get_body_footprint(variant)
                    .into_iter()
                    .map(|aop| aop.map_place(|p| p.replace_place(&pred_self_place, place)))
                    .collect();

                for contained_place in &places_in_pred {
                    assert!(!state.contains_perm(contained_place));
                }

                // Simulate unfolding of `place`
                state.remove_pred(place, perm_amount)?;
                state.insert_all_perms(places_in_pred.into_iter())?;
            }

            &vir::Stmt::BeginFrame => state.begin_frame(),

            &vir::Stmt::EndFrame => state.end_frame()?,

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

                let rhs_is_array = rhs_place.get_type().name().starts_with("Array$");

                // And we create permissions for the rhs
                let new_acc_places: Vec<_> = if rhs_is_array {
                    // all permissions are on the pred
                    vec![]
                } else {
                    original_state
                        .acc()
                        .iter()
                        .filter(|(p, _)| p.has_proper_prefix(lhs_place))
                        .map(|(p, perm_amount)| {
                            (p.clone().replace_place(&lhs_place, rhs_place), *perm_amount)
                        })
                        .filter(|(p, _)| !p.is_local())
                        .collect()
                };

                let new_pred_places: Vec<_> = if rhs_is_array {
                    vec![
                        // arrays regained here are always write, read-only does not generate
                        // wands/permissions that need to be restored
                        (
                            rhs_place.clone(),
                            vir::PermAmount::Write,
                        )
                    ]
                } else {
                    original_state
                        .pred()
                        .iter()
                        .filter(|(p, _)| p.has_prefix(lhs_place))
                        .map(|(p, perm_amount)| {
                            (p.clone().replace_place(&lhs_place, rhs_place), *perm_amount)
                        })
                        .collect()
                };

                // assert!(
                //     (lhs_place == rhs_place) || !(new_acc_places.is_empty() && new_pred_places.is_empty()),
                //     "Statement '{}' did not restore any permission in state with acc {{\n{}\n}}\nand pred {{\n{}\n}}",
                //     self,
                //     original_state.display_acc(),
                //     original_state.display_pred()
                // );

                trace!("new_acc_places: {:?}", new_acc_places);
                trace!("new_pred_places: {:?}", new_pred_places);

                state.insert_all_acc(new_acc_places.into_iter())?;
                state.insert_all_pred(new_pred_places.into_iter())?;

                // Move also the acc permission if the rhs is old.
                if state.contains_acc(lhs_place) && !state.contains_acc(rhs_place) {
                    if rhs_place.is_old() {
                        debug!("Moving acc({}) to acc({}) state.", lhs_place, rhs_place);
                        state.insert_acc(
                            rhs_place.clone(),
                            state.acc().get(lhs_place).unwrap().clone(),
                        )?;
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
                    )?;
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
                exhale_expr(rhs, state, predicates)?;
                inhale_expr(lhs, state, predicates)?;
            }

            &vir::Stmt::ApplyMagicWand(vir::Expr::MagicWand(ref lhs, ref rhs, _, _), _) => {
                exhale_expr(lhs, state, predicates)?;
                inhale_expr(rhs, state, predicates)?;
            }

            &vir::Stmt::ExpireBorrows(ref _dag) => {
                // TODO: #133
            }

            &vir::Stmt::Downcast(ref enum_place, ref variant_field) => {
                if let Some(found_variant) = find_unfolded_variant(state, enum_place) {
                    // The enum has already been downcasted.
                    debug_assert!(variant_field.name.ends_with(found_variant.get_variant_name()));
                    debug!("Place {} has already been downcasted to {}", enum_place, variant_field);
                } else {
                    debug!("Downcast {} to {}", enum_place, variant_field);
                    let predicate_name = enum_place.typed_ref_name().unwrap();
                    let predicate = predicates.get(&predicate_name).unwrap();
                    if let vir::Predicate::Enum(enum_predicate) = predicate {
                        let discriminant_place = enum_place.clone()
                            .field(enum_predicate.discriminant_field.clone());
                        if let Some(perm_amount) = state.acc().get(&discriminant_place).copied() {
                            // Add the permissions of the variant
                            let self_place: vir::Expr = enum_predicate.this.clone().into();
                            let variant_footprint: Vec<_> = enum_predicate.get_variant_footprint(
                                &variant_field.into()
                            ).into_iter().map(|perm|
                                // Update the permissiona and replace `self` with `enum_place`
                                perm.update_perm_amount(perm_amount)
                                    .map_place(|place| place.replace_place(&self_place, enum_place))
                            ).collect();
                            trace!("Downcast adds variant's footprint {:?}", variant_footprint);
                            state.insert_all_perms(variant_footprint.into_iter())?;
                        } else {
                            debug!("Place {} has not been unfolded yet", discriminant_place);
                        }
                    } else {
                        unreachable!()
                    }
                }
            }

            ref x => unimplemented!("{}", x),
        }
        Ok(())
    }
}
