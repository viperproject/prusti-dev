// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::Predicates;
use crate::encoder::foldunfold::{
    footprint::*,
    perm::{Perm::*, *},
};
use log::{debug, trace};
use rustc_hash::FxHashSet;
use std::iter::FromIterator;
use vir_crate::polymorphic::{self as vir, PermAmount};

pub trait RequiredStmtPermissionsGetter {
    /// Returns the permissions required for the statement to be well-defined.
    /// The result can be an over-approximation.
    fn get_required_permissions(&self, predicates: &Predicates) -> FxHashSet<Perm>;
}

pub trait RequiredExprPermissionsGetter {
    /// Compute the required permissions that the *statement* containing the expression has.
    /// This is needed to appropriately generate fold statements in impure code, before the
    /// statement containing the `self` expression, because Viper has no "folding" expressions.
    fn get_required_stmt_permissions(&self, preds: &Predicates) -> FxHashSet<Perm>;

    fn get_all_required_expr_permissions(&self, predicates: &Predicates) -> FxHashSet<Perm>;

    /// Compute the required permissions that the root of the expression has.
    /// If subexpressions have requirements that can be satisfied by generating unfolding
    /// expressions in the subexpressions, then those requirements should *not* be returned by
    /// this method.
    fn get_required_expr_permissions(&self, predicates: &Predicates) -> FxHashSet<Perm>;
}

impl<'a, A: RequiredStmtPermissionsGetter> RequiredStmtPermissionsGetter for &'a A {
    fn get_required_permissions(&self, predicates: &Predicates) -> FxHashSet<Perm> {
        (*self).get_required_permissions(predicates)
    }
}

impl<'a, A: RequiredExprPermissionsGetter> RequiredExprPermissionsGetter for &'a A {
    fn get_required_stmt_permissions(&self, predicates: &Predicates) -> FxHashSet<Perm> {
        (*self).get_required_stmt_permissions(predicates)
    }
    fn get_all_required_expr_permissions(&self, predicates: &Predicates) -> FxHashSet<Perm> {
        (*self).get_all_required_expr_permissions(predicates)
    }
    fn get_required_expr_permissions(&self, predicates: &Predicates) -> FxHashSet<Perm> {
        (*self).get_required_expr_permissions(predicates)
    }
}

impl RequiredStmtPermissionsGetter for vir::Stmt {
    fn get_required_permissions(&self, predicates: &Predicates) -> FxHashSet<Perm> {
        match self {
            &vir::Stmt::Comment(_) | &vir::Stmt::Label(_) => FxHashSet::default(),

            &vir::Stmt::Inhale(vir::Inhale { ref expr }) => perm_difference(
                expr.get_required_stmt_permissions(predicates),
                expr.get_footprint(predicates),
            ),

            &vir::Stmt::Exhale(vir::Exhale {
                ref expr,
                ref position,
            })
            | &vir::Stmt::Assert(vir::Assert {
                ref expr,
                ref position,
            })
            | &vir::Stmt::Obtain(vir::Obtain {
                ref expr,
                ref position,
            }) => {
                let perms = expr.get_required_stmt_permissions(predicates);
                perms
                    .into_iter()
                    .map(|perm| perm.set_default_pos(*position))
                    .collect()
            }

            &vir::Stmt::MethodCall(vir::MethodCall {
                ref arguments,
                ref targets,
                ..
            }) => {
                // Preconditions and postconditions are empty
                assert!(arguments.is_empty());
                FxHashSet::from_iter(
                    targets
                        .iter()
                        .cloned()
                        .map(|v| Acc(vir::Expr::local(v), PermAmount::Write)),
                )
            }

            &vir::Stmt::Assign(vir::Assign {
                ref target,
                ref source,
                ..
            }) => {
                // Here we use `get_all_required_expr_permissions` instead of
                // `get_required_stmt_permissions` because `ApplyOnState::apply_on_state` doesn't
                // currently support unfoldings on the RHS.
                let mut res = source.get_all_required_expr_permissions(predicates);
                res.insert(Acc(target.clone(), PermAmount::Write));
                res
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

                // We want to temporarily unfold place
                let predicate_type = place.get_type();
                let predicate = predicates.get(predicate_type).unwrap();

                let pred_self_place: vir::Expr = predicate.self_place();
                let places_in_pred: FxHashSet<Perm> = predicate
                    .get_body_footprint(enum_variant)
                    .into_iter()
                    .map(|perm| {
                        // TODO polymorphic: add replace_place
                        perm.map_place(|p| p.replace_place(&pred_self_place, place))
                            .init_perm_amount(permission)
                    })
                    .collect();

                places_in_pred
            }

            &vir::Stmt::Unfold(vir::Unfold {
                ref arguments,
                permission,
                ..
            }) => {
                assert_eq!(arguments.len(), 1);
                let place = &arguments[0];
                debug_assert!(place.is_place());
                place
                    .get_required_stmt_permissions(predicates)
                    .into_iter()
                    .map(|perm| perm.init_perm_amount(permission))
                    .collect()
            }

            &vir::Stmt::BeginFrame(_) | &vir::Stmt::EndFrame(_) => FxHashSet::default(),

            &vir::Stmt::TransferPerm(vir::TransferPerm {
                ref left,
                unchecked,
                ..
            }) => {
                let mut res = FxHashSet::default();
                if !unchecked {
                    res.insert(Acc(left.clone(), PermAmount::Read));
                }
                res
            }

            &vir::Stmt::PackageMagicWand(..) => {
                // We model the magic wand as "assert lhs; stmts; exhale rhs"
                FxHashSet::default()
            }

            &vir::Stmt::ApplyMagicWand(vir::ApplyMagicWand {
                magic_wand: vir::Expr::MagicWand(vir::MagicWand { ref left, .. }),
                ..
            }) => {
                // We model the magic wand as "assert lhs; inhale rhs"
                left.get_required_stmt_permissions(predicates)
            }

            &vir::Stmt::ExpireBorrows(vir::ExpireBorrows { dag: ref _dag }) => {
                FxHashSet::default() // TODO: #133
            }

            &vir::Stmt::If(vir::If {
                ref guard,
                ref then_stmts,
                ref else_stmts,
            }) => {
                let guard_reqs = guard.get_required_stmt_permissions(predicates);
                let then_reqs: FxHashSet<_> = then_stmts
                    .iter()
                    .flat_map(|x| x.get_required_permissions(predicates))
                    .collect();
                let else_reqs: FxHashSet<_> = else_stmts
                    .iter()
                    .flat_map(|x| x.get_required_permissions(predicates))
                    .collect();
                let then_else_reqs = then_reqs.intersection(&else_reqs).cloned().collect();
                guard_reqs.union(&then_else_reqs).cloned().collect()
            }

            &vir::Stmt::Downcast(vir::Downcast { ref base, .. }) => {
                base.get_required_stmt_permissions(predicates)
            }

            ref x => unimplemented!("{}", x),
        }
    }
}

impl RequiredExprPermissionsGetter for vir::Expr {
    fn get_required_stmt_permissions(&self, preds: &Predicates) -> FxHashSet<Perm> {
        trace!("[enter] get_required_stmt_permissions(expr={})", self);
        let reqs = self.get_all_required_expr_permissions(preds)
            .into_iter()
            .filter(|p| p.is_pred())
            .collect();
        trace!("[exit] get_required_stmt_permissions(expr={}) {:#?}", self, reqs);
        reqs
    }

    fn get_all_required_expr_permissions(&self, preds: &Predicates) -> FxHashSet<Perm> {
        trace!("[enter] get_all_required_expr_permissions(expr={})", self);
        let mut reqs: FxHashSet<Perm> = FxHashSet::default();

        reqs.extend(self.get_required_expr_permissions(preds));

        match self {
            vir::Expr::Variant(vir::Variant { base, .. })
            | vir::Expr::Field(vir::FieldExpr { base, .. })
            | vir::Expr::FieldAccessPredicate(vir::FieldAccessPredicate { base, .. })
            | vir::Expr::AddrOf(vir::AddrOf { base, .. })
            | vir::Expr::Cast(vir::Cast { base, .. })
            | vir::Expr::Downcast(vir::DowncastExpr { base, .. }) => {
                reqs.extend(base.get_all_required_expr_permissions(preds));
            }
            vir::Expr::ForAll(vir::ForAll { body, .. })
            | vir::Expr::Exists(vir::Exists { body, .. }) => {
                reqs.extend(body.get_all_required_expr_permissions(preds));
            }
            vir::Expr::UnaryOp(vir::UnaryOp { argument, .. })
            | vir::Expr::PredicateAccessPredicate(vir::PredicateAccessPredicate {
                argument, ..
            }) => {
                reqs.extend(argument.get_all_required_expr_permissions(preds));
            }
            vir::Expr::BinOp(vir::BinOp { left, right, .. })
            | vir::Expr::ContainerOp(vir::ContainerOp { left, right, .. }) => {
                reqs.extend(left.get_all_required_expr_permissions(preds));
                reqs.extend(right.get_all_required_expr_permissions(preds));
            }
            vir::Expr::Seq(vir::Seq { elements, .. }) => {
                reqs.extend(
                    elements
                        .iter()
                        .flat_map(|a| a.get_all_required_expr_permissions(preds)),
                );
            }
            vir::Expr::FuncApp(vir::FuncApp { arguments, .. })
            | vir::Expr::DomainFuncApp(vir::DomainFuncApp { arguments, .. }) => {
                reqs.extend(
                    arguments
                        .iter()
                        .flat_map(|a| a.get_all_required_expr_permissions(preds)),
                );
            }
            vir::Expr::Unfolding(vir::Unfolding {
                arguments,
                base,
                permission,
                variant,
                ..
            }) => {
                assert_eq!(arguments.len(), 1);
                let place = &arguments[0];
                debug_assert!(place.is_place());

                // We want to temporarly unfold `place`
                let predicate_type = place.get_type();
                let predicate = preds.get(predicate_type).unwrap();

                let pred_self_place: vir::Expr = predicate.self_place();
                let places_in_pred: FxHashSet<Perm> = predicate
                    .get_body_footprint(variant)
                    .into_iter()
                    .map(|aop| {
                        aop.map_place(|p| p.replace_place(&pred_self_place, place))
                            .update_perm_amount(*permission)
                    })
                    .collect();

                // Simulate temporary unfolding of `place`
                let expr_req_places = base.get_all_required_expr_permissions(preds);
                reqs.extend(perm_difference(expr_req_places, places_in_pred));
            }
            vir::Expr::Cond(vir::Cond {
                guard,
                then_expr,
                else_expr,
                ..
            }) => {
                reqs.extend(guard.get_all_required_expr_permissions(preds));
                reqs.extend(then_expr.get_all_required_expr_permissions(preds));
                reqs.extend(else_expr.get_all_required_expr_permissions(preds));
            }
            vir::Expr::LetExpr(vir::LetExpr { def, body, .. }) => {
                reqs.extend(def.get_all_required_expr_permissions(preds));
                reqs.extend(body.get_all_required_expr_permissions(preds));
            }
            _ => {}
        }

        trace!(
            "[exit] get_all_required_expr_permissions(expr={}) {:#?}",
            self,
            reqs
        );
        reqs
    }

    fn get_required_expr_permissions(&self, predicates: &Predicates) -> FxHashSet<Perm> {
        trace!("[enter] get_required_expr_permissions(expr={})", self);
        let permissions = match self {
            vir::Expr::Unfolding(vir::Unfolding {
                arguments,
                permission,
                ..
            }) => {
                assert_eq!(arguments.len(), 1);
                let place = &arguments[0];
                debug_assert!(place.is_place());
                vec![Pred(place.clone(), *permission)].into_iter().collect()
            }

            vir::Expr::PredicateAccessPredicate(vir::PredicateAccessPredicate {
                box argument,
                ..
            }) => {
                debug_assert!(argument.is_place());
                vec![
                    Pred(argument.clone(), PermAmount::Read),
                    Acc(argument.clone(), PermAmount::Read),
                ]
                .into_iter()
                .collect()
            }

            vir::Expr::FieldAccessPredicate(vir::FieldAccessPredicate { ref base, .. }) => {
                base.get_required_expr_permissions(predicates)
                    .into_iter()
                    .collect()
            }

            vir::Expr::LetExpr(vir::LetExpr {
                variable: _variable,
                def: _def,
                body: _body,
                ..
            }) => {
                unreachable!("Let expressions should be introduced after fold/unfold.");
            }

            vir::Expr::AddrOf(..) => unreachable!(),

            vir::Expr::Variant(..) => Some(Acc(self.clone(), PermAmount::Read))
                .into_iter()
                .collect(),

            vir::Expr::Field(..) => Some(Acc(self.clone(), PermAmount::Read))
                .into_iter()
                .collect(),

            vir::Expr::MagicWand(vir::MagicWand {
                left: ref _left,
                right: ref _right,
                borrow: ref _borrow,
                ..
            }) => {
                // Not exactly Viper's semantics
                FxHashSet::default()
            }

            vir::Expr::FuncApp(vir::FuncApp { ref arguments, .. })
            | vir::Expr::DomainFuncApp(vir::DomainFuncApp { ref arguments, .. }) => {
                arguments
                    .iter()
                    .flat_map(|arg| {
                        if arg.is_place() && arg.get_type().is_typed_ref_or_type_var() {
                            // FIXME: A hack: have unfolded Rust references in the precondition to
                            // simplify our life. A proper solution would be to look up the
                            // real function precondition.
                            if let Some(field_place) = arg.try_deref() {
                                Some(Pred(field_place, PermAmount::Read)).into_iter().collect()
                            } else {
                                Some(Pred(arg.clone(), PermAmount::Read)).into_iter().collect()
                            }
                        } else {
                            debug!("arg {} is not a place with type ref", arg);
                            arg.get_required_expr_permissions(predicates)
                        }
                    })
                    .collect()
            }

            vir::Expr::Downcast(vir::DowncastExpr { ref enum_place, .. }) => {
                let predicate_type = enum_place.get_type();
                let predicate = predicates.get(predicate_type).unwrap();
                if let vir::Predicate::Enum(enum_predicate) = predicate {
                    // We want to have the enum unfolded
                    enum_place
                        .clone()
                        .field(enum_predicate.discriminant_field.clone())
                        .get_required_expr_permissions(predicates)
                } else {
                    unreachable!()
                }
            }

            vir::Expr::SnapApp(..) => {
                unreachable!("Snapshots should be patched before fold/unfold. {:?}", self);
            }

            _ => FxHashSet::default(),
        };
        trace!(
            "[exit] get_required_expr_permissions(expr={}): {:#?}",
            self,
            permissions
        );
        permissions
    }
}
