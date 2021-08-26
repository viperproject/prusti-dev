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
use vir_crate::polymorphic as polymorphic_vir;
use std::collections::HashMap;
use log::{debug, trace};
use crate::encoder::foldunfold::FoldUnfoldError;
use crate::encoder::foldunfold::path_ctxt::find_unfolded_variant;

fn inhale_expr(expr: &polymorphic_vir::Expr, state: &mut State, predicates: &HashMap<String, polymorphic_vir::Predicate>)
    -> Result<(), FoldUnfoldError>
{
    state.insert_all_perms(
        expr.get_footprint(predicates)
            .into_iter()
            .filter(|p| !(p.is_local() && p.is_acc())),
    )
}

fn exhale_expr(expr: &polymorphic_vir::Expr, state: &mut State, predicates: &HashMap<String, polymorphic_vir::Predicate>)
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
    fn apply_on_state(&self, state: &mut State, predicates: &HashMap<String, polymorphic_vir::Predicate>)
        -> Result<(), FoldUnfoldError>;
}

impl ApplyOnState for polymorphic_vir::Stmt {
    fn apply_on_state(&self, state: &mut State, predicates: &HashMap<String, polymorphic_vir::Predicate>)
        -> Result<(), FoldUnfoldError>
    {
        debug!("apply_on_state '{}'", self);
        trace!("State acc before {{\n{}\n}}", state.display_acc());
        trace!("State pred before {{\n{}\n}}", state.display_pred());
        trace!("State moved before {{\n{}\n}}", state.display_moved());
        match self {
            &polymorphic_vir::Stmt::Comment(_)
            | &polymorphic_vir::Stmt::Label(_)
            | &polymorphic_vir::Stmt::Assert(_)
            | &polymorphic_vir::Stmt::Obtain(_) => {}

            &polymorphic_vir::Stmt::Inhale( polymorphic_vir::Inhale {ref expr} )  => {
                inhale_expr(expr, state, predicates)?;
            }

            &polymorphic_vir::Stmt::Exhale( polymorphic_vir::Exhale {ref expr, ..}) => {
                exhale_expr(expr, state, predicates)?;
            }

            &polymorphic_vir::Stmt::MethodCall( polymorphic_vir::MethodCall {ref targets, ..} ) => {
                // We know that in Prusti method's preconditions and postconditions are empty
                state.remove_moved_matching(|p| targets.contains(&p.get_base()));
                state.remove_pred_matching(|p| p.is_curr() && targets.contains(&p.get_base()));
                state.remove_acc_matching(|p| {
                    p.is_curr() && !p.is_local() && targets.contains(&p.get_base())
                });
            }

            &polymorphic_vir::Stmt::Assign( polymorphic_vir::Assign {ref target, ref source, kind} ) if kind != polymorphic_vir::AssignKind::Ghost => {
                debug_assert!(target.is_place());
                let original_state = state.clone();

                // Check the state of rhs.
                if kind != polymorphic_vir::AssignKind::Copy {
                    assert!(source.is_place());
                    assert!(source.get_type().is_typed_ref_or_type_var());

                    // Check that the rhs contains no moved paths
                    if state.is_prefix_of_some_moved(source) {
                        return Err(FoldUnfoldError::Unsupported("two-phase borrows are not supported".to_string()));
                    }
                    for prefix in source.all_proper_prefixes() {
                        assert!(!state.contains_pred(&prefix));
                    }
                }

                // Remove places that will not have a name
                state.remove_moved_matching(|p| p.has_prefix(&target));
                state.remove_pred_matching(|p| p.has_prefix(&target));
                state.remove_acc_matching(|p| p.has_proper_prefix(&target));

                // In case of move or borrowing, move permissions from the `rhs` to the `lhs`
                if source.is_place() && source.get_type().is_typed_ref_or_type_var() {
                    // This is a move assignemnt or the creation of a borrow
                    match kind {
                        polymorphic_vir::AssignKind::Move | polymorphic_vir::AssignKind::MutableBorrow(_) => {
                            // In Prusti, we lose permission on the rhs
                            state.remove_pred_matching(|p| p.has_prefix(&source));
                            state.remove_acc_matching(|p| {
                                p.has_proper_prefix(&source) && !p.is_local()
                            });

                            // We also lose permission on the lhs
                            state.remove_pred_matching(|p| p.has_prefix(&target));
                            state.remove_acc_matching(|p| {
                                p.has_proper_prefix(&target) && !p.is_local()
                            });

                            // And we create permissions for the lhs
                            let new_acc_places = original_state
                                .acc()
                                .iter()
                                .filter(|(p, _)| p.has_proper_prefix(&source))
                                .map(|(p, perm_amount)| {
                                    (p.clone().replace_place(&source, target), *perm_amount)
                                })
                                .filter(|(p, _)| !p.is_local());
                            state.insert_all_acc(new_acc_places)?;

                            let new_pred_places = original_state
                                .pred()
                                .iter()
                                .filter(|(p, _)| p.has_prefix(&source))
                                .map(|(p, perm_amount)| {
                                    (p.clone().replace_place(&source, target), *perm_amount)
                                });
                            state.insert_all_pred(new_pred_places)?;

                            // Finally, mark the rhs as moved
                            if !source.has_prefix(target) {
                                state.insert_moved(source.clone());
                            }
                        }
                        polymorphic_vir::AssignKind::SharedBorrow(_) => {
                            // We lose permission on the lhs
                            state.remove_pred_matching(|p| p.has_prefix(&target));
                            state.remove_acc_matching(|p| {
                                p.has_proper_prefix(&target) && !p.is_local()
                            });
                        }
                        polymorphic_vir::AssignKind::Ghost | polymorphic_vir::AssignKind::Copy => {
                            unreachable!();
                        }
                    }
                } else {
                    // This is not move assignemnt or the creation of a borrow
                    assert!(
                        match kind {
                            polymorphic_vir::AssignKind::Copy => true,
                            _ => false,
                        },
                        "Unexpected assignment kind: {:?}",
                        kind
                    );
                }
            }

            &polymorphic_vir::Stmt::Assign( polymorphic_vir::Assign {kind: polymorphic_vir::AssignKind::Ghost, ..} )  => {
                // Do nothing.
            }

            &polymorphic_vir::Stmt::Fold( polymorphic_vir::Fold {ref arguments, permission, ref enum_variant, ..} ) => {
                assert_eq!(arguments.len(), 1);
                let place = &arguments[0];
                debug_assert!(place.is_place());
                assert!(!state.contains_pred(place));
                assert!(!state.is_prefix_of_some_moved(place));

                // We want to fold place
                let predicate_name = place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: polymorphic_vir::Expr = predicate.self_place();
                let places_in_pred: Vec<Perm> = predicate
                    .get_body_footprint(enum_variant)
                    .into_iter()
                    .map(|perm| {
                        perm.map_place(|p| p.replace_place(&pred_self_place, place))
                            .init_perm_amount(permission)
                    })
                    .collect();

                // Commented due to the presence of implications in the body of predicates
                //for contained_place in &places_in_pred {
                //    assert!(state.contains(contained_place));
                //}

                // Simulate folding of `place`
                state.remove_all_perms(places_in_pred.iter())?;
                state.insert_pred(place.clone(), permission)?;
            }

            &polymorphic_vir::Stmt::Unfold( polymorphic_vir::Unfold {ref arguments, permission, ref enum_variant, ..} ) => {
                assert_eq!(arguments.len(), 1);
                let place = &arguments[0];
                debug_assert!(place.is_place());
                assert!(state.contains_pred(place));
                assert!(!state.is_prefix_of_some_moved(place));

                // We want to unfold place
                let predicate_name = place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: polymorphic_vir::Expr = predicate.self_place();
                let places_in_pred: Vec<_> = predicate
                    .get_body_footprint(enum_variant)
                    .into_iter()
                    .map(|aop| aop.map_place(|p| p.replace_place(&pred_self_place, place)))
                    .collect();

                for contained_place in &places_in_pred {
                    assert!(!state.contains_perm(contained_place));
                }

                // Simulate unfolding of `place`
                state.remove_pred(place, permission)?;
                state.insert_all_perms(places_in_pred.into_iter())?;
            }

            &polymorphic_vir::Stmt::BeginFrame(_) => state.begin_frame(),

            &polymorphic_vir::Stmt::EndFrame(_) => state.end_frame()?,

            &polymorphic_vir::Stmt::TransferPerm( polymorphic_vir::TransferPerm {ref left, ref right, unchecked} ) => {
                let original_state = state.clone();

                debug_assert!(
                    !left.is_simple_place() || state.is_prefix_of_some_acc(left) || state.is_prefix_of_some_pred(left),
                    "The fold/unfold state does not contain the permission for an expiring borrow: {}",
                    left
                );
                /*assert!(
                    state.is_prefix_of_some_pred(lhs_place),
                    "The fold/unfold state does not contain the permission for an expiring borrow: {}",
                    lhs_place
                );*/
                debug_assert!(left.get_type().is_typed_ref_or_type_var());
                debug_assert!(right.get_type().is_typed_ref_or_type_var());
                debug_assert_eq!(left.get_type(), right.get_type());
                //debug_assert!(!state.is_proper_prefix_of_some_acc(rhs_place));
                //debug_assert!(!state.is_prefix_of_some_pred(rhs_place));
                //debug_assert!(!lhs_place.is_curr() || !state.is_prefix_of_some_moved(lhs_place));

                // Restore permissions from the `lhs` to the `rhs`

                // In Prusti, lose permission from the lhs and rhs
                state.remove_pred_matching(|p| p.has_prefix(&left));
                state.remove_acc_matching(|p| p.has_proper_prefix(&left) && !p.is_local());
                state.remove_pred_matching(|p| p.has_prefix(&right));
                state.remove_acc_matching(|p| p.has_proper_prefix(&right) && !p.is_local());

                // The rhs is no longer moved
                state.remove_moved_matching(|p| p.has_prefix(right));

                let rhs_is_array = right.get_type().name().starts_with("Array$");

                // And we create permissions for the rhs
                let new_acc_places: Vec<_> = if rhs_is_array {
                    // all permissions are on the pred
                    vec![]
                } else {
                    original_state
                        .acc()
                        .iter()
                        .filter(|(p, _)| p.has_proper_prefix(left))
                        .map(|(p, perm_amount)| {
                            (p.clone().replace_place(&left, right), *perm_amount)
                        })
                        .filter(|(p, _)| !p.is_local())
                        .collect()
                };

                let new_pred_places: Vec<_> = if rhs_is_array {
                    vec![
                        // arrays regained here are always write, read-only does not generate
                        // wands/permissions that need to be restored
                        (
                            right.clone(),
                            polymorphic_vir::PermAmount::Write,
                        )
                    ]
                } else {
                    original_state
                        .pred()
                        .iter()
                        .filter(|(p, _)| p.has_prefix(left))
                        .map(|(p, perm_amount)| {
                            (p.clone().replace_place(&left, right), *perm_amount)
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
                if state.contains_acc(left) && !state.contains_acc(right) {
                    if right.is_old() {
                        debug!("Moving acc({}) to acc({}) state.", left, right);
                        state.insert_acc(
                            right.clone(),
                            state.acc().get(left).unwrap().clone(),
                        )?;
                        if !left.is_local() && !left.is_curr() {
                            state.remove_acc_place(left);
                        }
                    }
                }

                // Remove the lhs access permission if it was old.
                if state.contains_acc(left) && left.is_old() {
                    state.remove_acc_place(left);
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
                if !left.has_prefix(right) &&   // Maybe this is always true?
                        !unchecked
                {
                    state.insert_moved(left.clone());
                }
            }

            &polymorphic_vir::Stmt::PackageMagicWand( polymorphic_vir::PackageMagicWand {
                magic_wand: polymorphic_vir::Expr::MagicWand( polymorphic_vir::MagicWand {ref left, ref right, ..} ),
                ..
            }) => {
                // The semantics of the statements is handled in `foldunfold/mod.rs`.
                //for stmt in package_stmts {
                //    stmt.apply_on_state(state, predicates);
                //}
                exhale_expr(right, state, predicates)?;
                inhale_expr(left, state, predicates)?;
            }

            &polymorphic_vir::Stmt::ApplyMagicWand( polymorphic_vir::ApplyMagicWand {
                magic_wand: polymorphic_vir::Expr::MagicWand( polymorphic_vir::MagicWand {ref left, ref right, ..}),
                ..
            }) => {
                exhale_expr(left, state, predicates)?;
                inhale_expr(right, state, predicates)?;
            }

            &polymorphic_vir::Stmt::ExpireBorrows( polymorphic_vir::ExpireBorrows {dag: ref _dag} ) => {
                // TODO: #133
            }

            &polymorphic_vir::Stmt::Downcast( polymorphic_vir::Downcast {base: ref enum_place, ref field} ) => {
                if let Some(found_variant) = find_unfolded_variant(state, enum_place) {
                    // The enum has already been downcasted.
                    debug_assert!(field.name.ends_with(found_variant.get_variant_name()));
                    debug!("Place {} has already been downcasted to {}", enum_place, field);
                } else {
                    debug!("Downcast {} to {}", enum_place, field);
                    let predicate_name = enum_place.typed_ref_name().unwrap();
                    let predicate = predicates.get(&predicate_name).unwrap();
                    if let polymorphic_vir::Predicate::Enum(enum_predicate) = predicate {
                        let discriminant_place = enum_place.clone()
                            .field(enum_predicate.discriminant_field.clone());
                        if let Some(perm_amount) = state.acc().get(&discriminant_place).copied() {
                            // Add the permissions of the variant
                            let self_place: polymorphic_vir::Expr = enum_predicate.this.clone().into();
                            let variant_footprint: Vec<_> = enum_predicate.get_variant_footprint(
                                &field.into()
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
