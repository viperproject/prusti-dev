// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{
    places_utils::{union, union3},
    Predicates,
};
use crate::encoder::foldunfold::{
    footprint::*,
    perm::{Perm::*, *},
    places_utils::ancestors,
};
use log::{debug, trace};
use std::{
    collections::{HashMap, HashSet},
    iter::FromIterator,
};
use vir_crate::polymorphic::{self as vir, PermAmount};

pub trait RequiredPermissionsGetter {
    /// Returns the permissions required for the expression/statement to be well-defined.
    /// The result might be an over-approximation, as in the `vir::Expr::FuncApp` case.
    fn get_required_permissions(
        &self,
        predicates: &Predicates,
        old_exprs: &HashMap<String, Vec<vir::Expr>>,
    ) -> HashSet<Perm>;
}

impl<'a, A: RequiredPermissionsGetter> RequiredPermissionsGetter for &'a A {
    fn get_required_permissions(
        &self,
        predicates: &Predicates,
        old_exprs: &HashMap<String, Vec<vir::Expr>>,
    ) -> HashSet<Perm> {
        (*self).get_required_permissions(predicates, old_exprs)
    }
}

impl<'a, A: RequiredPermissionsGetter> RequiredPermissionsGetter for Vec<A> {
    fn get_required_permissions(
        &self,
        predicates: &Predicates,
        old_exprs: &HashMap<String, Vec<vir::Expr>>,
    ) -> HashSet<Perm> {
        self.iter().fold(HashSet::new(), |res, x| {
            res.union(&x.get_required_permissions(predicates, old_exprs))
                .cloned()
                .collect()
        })
    }
}

impl RequiredPermissionsGetter for vir::Stmt {
    fn get_required_permissions(
        &self,
        predicates: &Predicates,
        old_exprs: &HashMap<String, Vec<vir::Expr>>,
    ) -> HashSet<Perm> {
        match self {
            &vir::Stmt::Comment(_) => HashSet::new(),

            &vir::Stmt::Label(vir::Label { ref label }) => {
                // A label has to ensure that all usages of labelled-old expressions can be
                // solved by unfolding, and not folding, permissions.
                if let Some(exprs) = old_exprs.get(label) {
                    exprs.get_required_permissions(predicates, old_exprs)
                } else {
                    HashSet::new()
                }
            }

            &vir::Stmt::Inhale(vir::Inhale { ref expr }) => {
                // footprint = used - inhaled
                perm_difference(
                    expr.get_required_permissions(predicates, old_exprs),
                    expr.get_footprint(predicates),
                )
            }

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
                let perms = expr.get_required_permissions(predicates, old_exprs);
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
                HashSet::from_iter(
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
                let mut res = source.get_required_permissions(predicates, old_exprs);
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
                let places_in_pred: HashSet<Perm> = predicate
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
                    .get_required_permissions(predicates, old_exprs)
                    .into_iter()
                    .map(|perm| perm.init_perm_amount(permission))
                    .collect()
            }

            &vir::Stmt::BeginFrame(_) | &vir::Stmt::EndFrame(_) => HashSet::new(),

            &vir::Stmt::TransferPerm(vir::TransferPerm {
                ref left,
                unchecked,
                ..
            }) => {
                let mut res = HashSet::new();
                if !unchecked {
                    res.insert(Acc(left.clone(), PermAmount::Read));
                }
                res
            }

            &vir::Stmt::PackageMagicWand(..) => {
                // We model the magic wand as "assert lhs; stmts; exhale rhs"
                HashSet::new()
            }

            &vir::Stmt::ApplyMagicWand(vir::ApplyMagicWand {
                magic_wand: vir::Expr::MagicWand(vir::MagicWand { ref left, .. }),
                ..
            }) => {
                // We model the magic wand as "assert lhs; inhale rhs"
                left.get_required_permissions(predicates, old_exprs)
            }

            &vir::Stmt::ExpireBorrows(vir::ExpireBorrows { dag: ref _dag }) => {
                HashSet::new() // TODO: #133
            }

            &vir::Stmt::If(vir::If {
                ref guard,
                ref then_stmts,
                ref else_stmts,
            }) => {
                let guard_reqs = guard.get_required_permissions(predicates, old_exprs);
                let then_reqs = then_stmts.get_required_permissions(predicates, old_exprs);
                let else_reqs = else_stmts.get_required_permissions(predicates, old_exprs);
                let then_else_reqs = then_reqs.intersection(&else_reqs).cloned().collect();
                guard_reqs.union(&then_else_reqs).cloned().collect()
            }

            &vir::Stmt::Downcast(vir::Downcast {
                ref base,
                ref field,
            }) => {
                // Delegate
                vir::Expr::downcast(true.into(), base.clone(), field.clone())
                    .get_required_permissions(predicates, old_exprs)
            }

            ref x => unimplemented!("{}", x),
        }
    }
}

impl RequiredPermissionsGetter for vir::Expr {
    fn get_required_permissions(
        &self,
        predicates: &Predicates,
        old_exprs: &HashMap<String, Vec<vir::Expr>>,
    ) -> HashSet<Perm> {
        trace!("[enter] get_required_permissions(expr={})", self);
        let permissions = match self {
            vir::Expr::Const(..) => HashSet::new(),

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

                // We want to temporarly unfold place
                let predicate_type = place.get_type();
                let predicate = predicates.get(predicate_type).unwrap();

                let pred_self_place: vir::Expr = predicate.self_place();
                let places_in_pred: HashSet<Perm> = predicate
                    .get_body_footprint(variant)
                    .into_iter()
                    .map(|aop| {
                        aop.map_place(|p| p.replace_place(&pred_self_place, place))
                            .update_perm_amount(*permission)
                    })
                    .collect();

                // Simulate temporary unfolding of `place`
                let expr_req_places = base.get_required_permissions(predicates, old_exprs);
                let mut req_places: HashSet<_> = perm_difference(expr_req_places, places_in_pred);
                req_places.insert(Pred(place.clone(), *permission));
                req_places.into_iter().collect()
            }

            vir::Expr::LabelledOld(vir::LabelledOld {
                label: ref _label,
                base: ref _base,
                ..
            }) => HashSet::new(),

            vir::Expr::PredicateAccessPredicate(vir::PredicateAccessPredicate {
                box argument,
                ..
            }) => {
                debug_assert!(argument.is_place());
                let epsilon = PermAmount::Read;
                let result = match argument.get_label() {
                    None => {
                        if argument.is_old() {
                            vec![Pred(argument.clone(), epsilon)].into_iter().collect()
                        } else {
                            vec![
                                Pred(argument.clone(), epsilon),
                                Acc(argument.clone(), epsilon),
                            ]
                            .into_iter()
                            .collect()
                        }
                    }
                    Some(label) => {
                        if argument.is_old() {
                            vec![Pred(argument.clone().old(label), epsilon)]
                                .into_iter()
                                .collect()
                        } else {
                            vec![
                                Pred(argument.clone().old(label), epsilon),
                                Acc(argument.clone().old(label), epsilon),
                            ]
                            .into_iter()
                            .collect()
                        }
                    }
                };
                result
            }

            vir::Expr::FieldAccessPredicate(vir::FieldAccessPredicate { ref base, .. }) => base
                .get_required_permissions(predicates, old_exprs)
                .into_iter()
                .collect(),

            vir::Expr::UnaryOp(vir::UnaryOp { ref argument, .. }) => {
                argument.get_required_permissions(predicates, old_exprs)
            }

            vir::Expr::BinOp(vir::BinOp {
                box left,
                box right,
                ..
            }) => vec![left, right].get_required_permissions(predicates, old_exprs),

            vir::Expr::ContainerOp(vir::ContainerOp {
                box left,
                box right,
                ..
            }) => vec![left, right].get_required_permissions(predicates, old_exprs),

            vir::Expr::Seq(vir::Seq { elements, .. }) => {
                elements.get_required_permissions(predicates, old_exprs)
            }

            vir::Expr::Cond(vir::Cond {
                box guard,
                box then_expr,
                box else_expr,
                ..
            }) => vec![guard, then_expr, else_expr].get_required_permissions(predicates, old_exprs),

            vir::Expr::LetExpr(vir::LetExpr {
                variable: _variable,
                def: _def,
                body: _body,
                ..
            }) => {
                unreachable!("Let expressions should be introduced after fold/unfold.");
            }

            vir::Expr::ForAll(vir::ForAll {
                variables,
                box body,
                ..
            })
            | vir::Expr::Exists(vir::Exists {
                variables,
                box body,
                ..
            }) => {
                assert!(variables
                    .iter()
                    .all(|var| !var.typ.is_typed_ref_or_type_var()));

                let vars_places: HashSet<_> = variables
                    .iter()
                    .map(|var| Acc(vir::Expr::local(var.clone()), PermAmount::Write))
                    .collect();
                perm_difference(
                    body.get_required_permissions(predicates, old_exprs),
                    vars_places,
                )
            }

            vir::Expr::Local(..) => HashSet::new(),

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
                HashSet::new()
            }

            vir::Expr::FuncApp(vir::FuncApp { ref arguments, .. })
            | vir::Expr::DomainFuncApp(vir::DomainFuncApp { ref arguments, .. }) => {
                arguments
                    .iter()
                    .map(|arg| {
                        if arg.is_place() && arg.get_type().is_typed_ref_or_type_var() {
                            // FIXME: A hack: have unfolded Rust references in the precondition to
                            // simplify our life. A proper solution would be to look up the
                            // real function precondition.
                            if let Some(field_place) = arg.try_deref() {
                                vir::Expr::and(
                                    vir::Expr::acc_permission(
                                        field_place.clone(),
                                        PermAmount::Read,
                                    ),
                                    vir::Expr::pred_permission(field_place, PermAmount::Read)
                                        .unwrap(),
                                )
                            } else {
                                let typ = arg.get_type();
                                vir::Expr::predicate_access_predicate(
                                    typ.clone(),
                                    arg.clone(),
                                    PermAmount::Read,
                                )
                            }
                        } else {
                            debug!("arg {} is not a place with type ref", arg);
                            arg.clone()
                        }
                    })
                    .collect::<Vec<_>>()
                    .get_required_permissions(predicates, old_exprs)
            }

            vir::Expr::InhaleExhale(..) => HashSet::new(),

            vir::Expr::Downcast(vir::DowncastExpr { ref enum_place, .. }) => {
                let predicate_type = enum_place.get_type();
                let predicate = predicates.get(predicate_type).unwrap();
                if let vir::Predicate::Enum(enum_predicate) = predicate {
                    // We want to have the enum unfolded
                    enum_place
                        .clone()
                        .field(enum_predicate.discriminant_field.clone())
                        .get_required_permissions(predicates, old_exprs)
                } else {
                    unreachable!()
                }
            }

            vir::Expr::SnapApp(..) => {
                unreachable!("Snapshots should be patched before fold/unfold. {:?}", self);
            }
        };
        trace!(
            "[exit] get_required_permissions(expr={}): {:#?}",
            self,
            permissions
        );
        permissions
    }
}
