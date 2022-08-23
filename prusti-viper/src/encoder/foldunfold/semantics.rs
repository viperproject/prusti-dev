// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::Predicates;
use crate::encoder::foldunfold::{
    footprint::*, path_ctxt::find_unfolded_variant, perm::*, state::*, FoldUnfoldError,
};
use log::trace;

use vir_crate::polymorphic as vir;

fn inhale_expr(
    expr: &vir::Expr,
    state: &mut State,
    predicates: &Predicates,
) -> Result<(), FoldUnfoldError> {
    state.insert_all_perms(
        expr.get_footprint(predicates)
            .into_iter()
            .filter(|p| !(p.is_local() && p.is_acc())),
    )
}

fn exhale_expr(
    expr: &vir::Expr,
    state: &mut State,
    predicates: &Predicates,
) -> Result<(), FoldUnfoldError> {
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
    fn apply_on_state(
        &self,
        state: &mut State,
        predicates: &Predicates,
    ) -> Result<(), FoldUnfoldError>;
}

impl ApplyOnState for vir::Stmt {
    fn apply_on_state(
        &self,
        state: &mut State,
        predicates: &Predicates,
    ) -> Result<(), FoldUnfoldError> {
        trace!("apply_on_state '{}'", self);
        trace!("State acc before {{\n{}\n}}", state.display_acc());
        trace!("State pred before {{\n{}\n}}", state.display_pred());
        trace!("State moved before {{\n{}\n}}", state.display_moved());
        match self {
            &vir::Stmt::Comment(_)
            | &vir::Stmt::Label(_)
            | &vir::Stmt::Assert(_)
            | &vir::Stmt::Obtain(_) => {}

            &vir::Stmt::Inhale(vir::Inhale { ref expr }) => {
                inhale_expr(expr, state, predicates)?;
            }

            &vir::Stmt::Exhale(vir::Exhale { ref expr, .. }) => {
                exhale_expr(expr, state, predicates)?;
            }

            &vir::Stmt::MethodCall(vir::MethodCall { ref targets, .. }) => {
                // We know that in Prusti method's preconditions and postconditions are empty
                state.remove_moved_matching(|p| targets.contains(&p.get_base()));
                state.remove_pred_matching(|p| p.is_curr() && targets.contains(&p.get_base()));
                state.remove_acc_matching(|p| {
                    p.is_curr() && !p.is_local() && targets.contains(&p.get_base())
                });
            }

            &vir::Stmt::Assign(vir::Assign {
                ref target,
                ref source,
                kind,
            }) if kind != vir::AssignKind::Ghost => {
                debug_assert!(target.is_place());
                let original_state = state.clone();

                // Check the state of rhs.
                if kind != vir::AssignKind::Copy {
                    assert!(source.is_place());
                    assert!(source.get_type().is_typed_ref_or_type_var());

                    // Check that the rhs contains no moved paths
                    if state.is_prefix_of_some_moved(source) {
                        return Err(FoldUnfoldError::Unsupported(
                            "two-phase borrows are not supported".to_string(),
                        ));
                    }
                    for prefix in source.all_proper_prefixes() {
                        assert!(!state.contains_pred(&prefix));
                    }
                }

                // Remove places that will not have a name
                state.remove_moved_matching(|p| p.has_prefix(target));
                state.remove_pred_matching(|p| p.has_prefix(target));
                state.remove_acc_matching(|p| p.has_proper_prefix(target));

                // In case of move or borrowing, move permissions from the `rhs` to the `lhs`
                if source.is_place() && source.get_type().is_typed_ref_or_type_var() {
                    // This is a move assignemnt or the creation of a borrow
                    match kind {
                        vir::AssignKind::Move | vir::AssignKind::MutableBorrow(_) => {
                            // In Prusti, we lose permission on the rhs
                            state.remove_pred_matching(|p| p.has_prefix(source));
                            state.remove_acc_matching(|p| {
                                p.has_proper_prefix(source) && !p.is_local()
                            });

                            // We also lose permission on the lhs
                            state.remove_pred_matching(|p| p.has_prefix(target));
                            state.remove_acc_matching(|p| {
                                p.has_proper_prefix(target) && !p.is_local()
                            });

                            // And we create permissions for the lhs
                            let new_acc_places = original_state
                                .acc()
                                .iter()
                                .filter(|(p, _)| p.has_proper_prefix(source))
                                .map(|(p, perm_amount)| {
                                    (p.clone().replace_place(source, target), *perm_amount)
                                })
                                .filter(|(p, _)| !p.is_local());
                            state.insert_all_acc(new_acc_places)?;

                            let new_pred_places = original_state
                                .pred()
                                .iter()
                                .filter(|(p, _)| p.has_prefix(source))
                                .map(|(p, perm_amount)| {
                                    (p.clone().replace_place(source, target), *perm_amount)
                                });
                            state.insert_all_pred(new_pred_places)?;

                            // Finally, mark the rhs as moved
                            if !source.has_prefix(target) {
                                state.insert_moved(source.clone());
                            }
                        }
                        vir::AssignKind::SharedBorrow(_) => {
                            // We lose permission on the lhs
                            state.remove_pred_matching(|p| p.has_prefix(target));
                            state.remove_acc_matching(|p| {
                                p.has_proper_prefix(target) && !p.is_local()
                            });
                        }
                        vir::AssignKind::Ghost | vir::AssignKind::Copy => {
                            unreachable!();
                        }
                    }
                } else {
                    // This is not move assignemnt or the creation of a borrow
                    assert!(
                        matches!(kind, vir::AssignKind::Copy),
                        "Unexpected assignment kind: {:?}",
                        kind
                    );
                }
            }

            &vir::Stmt::Assign(vir::Assign {
                kind: vir::AssignKind::Ghost,
                ..
            }) => {
                // Do nothing.
            }

            &vir::Stmt::Fold(vir::Fold {
                ref arguments,
                permission,
                ref enum_variant,
                ..
            }) => {
                assert_eq!(arguments.len(), 1);
                let place = &arguments[0];
                debug_assert!(place.is_place());
                assert!(!state.contains_pred(place));
                assert!(!state.is_prefix_of_some_moved(place));

                // We want to fold place
                let predicate_type = place.get_type();
                let predicate = predicates.get(predicate_type).unwrap();

                let pred_self_place: vir::Expr = predicate.self_place();
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

            &vir::Stmt::Unfold(vir::Unfold {
                ref arguments,
                permission,
                ref enum_variant,
                ..
            }) => {
                assert_eq!(arguments.len(), 1);
                let self_place = &arguments[0];
                debug_assert!(self_place.is_place());
                assert!(state.contains_pred(self_place));
                assert!(!state.is_prefix_of_some_moved(self_place));

                // We want to unfold place
                let predicate_type = self_place.get_type();
                let predicate = predicates.get(predicate_type).unwrap();

                let pred_self_place: vir::Expr = predicate.self_place();
                let places_in_pred: Vec<_> = predicate
                    .get_body_footprint(enum_variant)
                    .into_iter()
                    .map(|perm| {
                        debug_assert_eq!(perm.get_perm_amount(), vir::PermAmount::Write);
                        // Scale permission
                        perm.map_place(|place| place.replace_place(&pred_self_place, self_place))
                            .update_perm_amount(permission)
                    })
                    .collect();

                for contained_place in &places_in_pred {
                    assert!(!state.contains_perm(contained_place));
                }

                // Simulate unfolding of `place`
                state.remove_pred(self_place, permission)?;
                state.insert_all_perms(places_in_pred.into_iter())?;
            }

            &vir::Stmt::BeginFrame(_) => state.begin_frame(),

            &vir::Stmt::EndFrame(_) => state.end_frame()?,

            &vir::Stmt::TransferPerm(vir::TransferPerm {
                ref left,
                ref right,
                unchecked,
            }) => {
                let original_state = state.clone();

                if !unchecked {
                    debug_assert!(
                        !left.is_simple_place() || state.is_prefix_of_some_acc(left) || state.is_prefix_of_some_pred(left),
                        "The fold/unfold state does not contain the permission for an expiring borrow: {}",
                        left
                    );
                }
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

                // Like `has_prefix`, but ignoring the labels if they are equal.
                fn old_has_prefix(this: &vir::Expr, other: &vir::Expr) -> bool {
                    if let (
                        vir::Expr::LabelledOld(vir::LabelledOld {
                            label: this_label,
                            base: this_base,
                            ..
                        }),
                        vir::Expr::LabelledOld(vir::LabelledOld {
                            label: other_label,
                            base: other_base,
                            ..
                        }),
                    ) = (this, other)
                    {
                        this_label == other_label && this_base.has_prefix(other_base)
                    } else {
                        this.has_prefix(other)
                    }
                }

                // Like `has_proper_prefix`, but ignoring the labels if they are equal.
                fn old_has_proper_prefix(this: &vir::Expr, other: &vir::Expr) -> bool {
                    if let (
                        vir::Expr::LabelledOld(vir::LabelledOld {
                            label: this_label,
                            base: this_base,
                            ..
                        }),
                        vir::Expr::LabelledOld(vir::LabelledOld {
                            label: other_label,
                            base: other_base,
                            ..
                        }),
                    ) = (this, other)
                    {
                        this_label == other_label && this_base.has_proper_prefix(other_base)
                    } else {
                        this.has_proper_prefix(other)
                    }
                }

                // Like `replace_place`, but ignoring the labels if they are equal.
                fn old_replace_place(
                    this: &vir::Expr,
                    target: &vir::Expr,
                    replacement: &vir::Expr,
                ) -> vir::Expr {
                    if let (
                        vir::Expr::LabelledOld(vir::LabelledOld {
                            label: this_label,
                            base: this_base,
                            ..
                        }),
                        vir::Expr::LabelledOld(vir::LabelledOld {
                            label: target_label,
                            base: target_base,
                            ..
                        }),
                    ) = (this, target)
                    {
                        if this_label == target_label {
                            if let vir::Expr::LabelledOld(repl_labelled) = replacement {
                                return vir::Expr::LabelledOld(vir::LabelledOld {
                                    base: box this_base
                                        .clone()
                                        .replace_place(target_base, repl_labelled.base.as_ref()),
                                    label: repl_labelled.label.clone(),
                                    position: repl_labelled.position,
                                });
                            } else {
                                return this_base.clone().replace_place(target_base, replacement);
                            }
                        }
                    }
                    this.clone().replace_place(target, replacement)
                }

                // In Prusti, lose permission from the lhs and rhs
                state.remove_pred_matching(|p| old_has_prefix(p, left));
                state.remove_acc_matching(|p| old_has_proper_prefix(p, left) && !p.is_local());
                state.remove_pred_matching(|p| old_has_prefix(p, right));
                state.remove_acc_matching(|p| old_has_proper_prefix(p, right) && !p.is_local());

                // The rhs is no longer moved
                state.remove_moved_matching(|p| old_has_prefix(p, right));

                // And we create permissions for the rhs
                let new_acc_places: Vec<_> = original_state
                    .acc()
                    .iter()
                    .filter(|(p, _)| old_has_proper_prefix(p, left))
                    .map(|(p, perm_amount)| (old_replace_place(p, left, right), *perm_amount))
                    .filter(|(p, _)| !p.is_local())
                    .collect();

                let new_pred_places: Vec<_> = original_state
                    .pred()
                    .iter()
                    .filter(|(p, _)| old_has_prefix(p, left))
                    .map(|(p, perm_amount)| (old_replace_place(p, left, right), *perm_amount))
                    .collect();

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
                if state.contains_acc(left) && !state.contains_acc(right) && right.is_old() {
                    trace!("Moving acc({}) to acc({}) state.", left, right);
                    state.insert_acc(right.clone(), *state.acc().get(left).unwrap())?;
                    if !left.is_local() && !left.is_curr() {
                        state.remove_acc_place(left);
                    }
                }

                // Remove the lhs access permission if it was old.
                if state.contains_acc(left) && left.is_old() {
                    state.remove_acc_place(left);
                }

                /*
                // Hack: Move also the acc permission
                if state.contains_acc(lhs_place) && !state.contains_acc(rhs_place) {
                    trace!("Moving acc({}) to acc({}) state.", lhs_place, rhs_place);
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
                if !old_has_prefix(left, right) &&   // Maybe this is always true?
                        !unchecked
                {
                    state.insert_moved(left.clone());
                }
            }

            &vir::Stmt::PackageMagicWand(vir::PackageMagicWand {
                magic_wand:
                    vir::Expr::MagicWand(vir::MagicWand {
                        ref left,
                        ref right,
                        ..
                    }),
                ..
            }) => {
                // The semantics of the statements is handled in `foldunfold/mod.rs`.
                //for stmt in package_stmts {
                //    stmt.apply_on_state(state, predicates);
                //}
                exhale_expr(right, state, predicates)?;
                inhale_expr(left, state, predicates)?;
            }

            &vir::Stmt::ApplyMagicWand(vir::ApplyMagicWand {
                magic_wand:
                    vir::Expr::MagicWand(vir::MagicWand {
                        ref left,
                        ref right,
                        ..
                    }),
                ..
            }) => {
                exhale_expr(left, state, predicates)?;
                inhale_expr(right, state, predicates)?;
            }

            &vir::Stmt::ExpireBorrows(vir::ExpireBorrows { dag: ref _dag }) => {
                // TODO: #133
            }

            &vir::Stmt::Downcast(vir::Downcast {
                base: ref enum_place,
                ref field,
            }) => {
                if let Some(found_variant) = find_unfolded_variant(state, enum_place) {
                    // The enum has already been downcasted.
                    debug_assert!(field.name.ends_with(found_variant.get_variant_name()));
                    trace!(
                        "Place {} has already been downcasted to {}",
                        enum_place,
                        field
                    );
                } else {
                    trace!("Downcast {} to {}", enum_place, field);
                    let predicate_type = enum_place.get_type();
                    let predicate = predicates.get(predicate_type).unwrap();
                    if let vir::Predicate::Enum(enum_predicate) = predicate {
                        let discriminant_place = enum_place
                            .clone()
                            .field(enum_predicate.discriminant_field.clone());
                        if let Some(perm_amount) = state.acc().get(&discriminant_place).copied() {
                            // Add the permissions of the variant
                            let self_place: vir::Expr = enum_predicate.this.clone().into();
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
                            trace!("Place {} has not been unfolded yet", discriminant_place);
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
