// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// TODO: Remove this and fix.
#![allow(deprecated)]

use encoder::foldunfold::perm::*;
use encoder::foldunfold::perm::Perm::*;
use encoder::vir;
use encoder::vir::Frac;
use encoder::vir::{Zero, One};
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;
use super::places_utils::{union, union3, difference, intersection};

pub trait RequiredPermissionsGetter {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<Perm>;
}

impl<'a, A: RequiredPermissionsGetter> RequiredPermissionsGetter for Vec<&'a A> {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<Perm> {
        self.iter().fold(
            HashSet::new(),
            |res, x| res.union(&x.get_required_permissions(predicates)).cloned().collect()
        )
    }
}

impl RequiredPermissionsGetter for Vec<vir::Expr> {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<Perm> {
        self.iter().fold(
            HashSet::new(),
            |res, x| res.union(&x.get_required_permissions(predicates)).cloned().collect()
        )
    }
}

impl RequiredPermissionsGetter for vir::Stmt {
    /// Returns the permissions required for the statement to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<Perm> {
        match self {
            &vir::Stmt::Comment(_) |
            &vir::Stmt::Label(_) => HashSet::new(),

            &vir::Stmt::Inhale(ref expr) => {
                // footprint = used - inhaled
                difference(
                    &expr.get_required_permissions(predicates),
                    &expr.get_permissions(predicates)
                )
            },

            &vir::Stmt::Exhale(ref expr, _) => expr.get_required_permissions(predicates),

            &vir::Stmt::Assert(ref expr, _) => expr.get_required_permissions(predicates),

            &vir::Stmt::MethodCall(_, ref args, ref vars) => {
                // Preconditions and postconditions are empty
                assert!(args.is_empty());
                HashSet::from_iter(vars.iter().cloned().map(|v| Acc(vir::Place::Base(v), Frac::one())))
            },

            &vir::Stmt::Assign(ref lhs_place, ref expr, kind) => {
                let mut res = expr.get_required_permissions(predicates);
                res.insert(Acc(lhs_place.clone(), Frac::one()));
                res
            },

            &vir::Stmt::Fold(_, ref args, frac) => {
                assert_eq!(args.len(), 1);
                let arg_place = &args[0].clone().as_place().unwrap();

                // We want to temporarly unfold arg_place
                let predicate_name = arg_place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: HashSet<Perm> = predicate.get_permissions().into_iter()
                    .map(
                        |perm| {
                            perm.map_place(
                                |place| place.replace_prefix(&pred_self_place, arg_place.clone())
                            )
                        }
                    ).collect();

                places_in_pred.into_iter().map(
                    |perm| perm * frac
                ).collect()
            },

            &vir::Stmt::Unfold(ref _pred_name, ref args, frac) => {
                assert_eq!(args.len(), 1);
                args[0].get_required_permissions(predicates)
                    .into_iter()
                    .map(
                        |perm| perm * frac
                    ).collect()
            },

            &vir::Stmt::Obtain(ref expr) => expr.get_required_permissions(predicates),

            &vir::Stmt::WeakObtain(ref expr) => HashSet::new(),

            &vir::Stmt::Havoc |
            &vir::Stmt::BeginFrame |
            &vir::Stmt::EndFrame |
            &vir::Stmt::TransferPerm(_, _) |
            &vir::Stmt::StopExpiringLoans => HashSet::new(),

            &vir::Stmt::ExpireBorrowsIf(ref guard, ref then_stmts, ref else_stmts) => {
                let mut permissions = guard.get_required_permissions(predicates);
                // A little optimization
                if !then_stmts.is_empty() && !else_stmts.is_empty() {
                    permissions = union(
                        &permissions,
                        &intersection(
                            &then_stmts[0].get_required_permissions(predicates),
                            &else_stmts[0].get_required_permissions(predicates),
                        )
                    );
                }
                permissions
            }

            &vir::Stmt::PackageMagicWand(ref lhs, ref _rhs, ref _package_stmts, ref _then_stmts) => {
                // We model the magic wand as "assert lhs; stmts; exhale rhs"
                lhs.get_required_permissions(predicates)
            }

            &vir::Stmt::ApplyMagicWand(ref lhs, ref _rhs) => {
                // We model the magic wand as "assert lhs; inhale rhs"
                lhs.get_required_permissions(predicates)
            }
        }
    }
}

impl vir::Stmt {
    /// Returns the permissions that the statement would prefer to have
    pub fn get_preferred_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<Perm> {
        match self {
            &vir::Stmt::Comment(_) |
            &vir::Stmt::Label(_) |
            &vir::Stmt::Inhale(_) |
            &vir::Stmt::Exhale(_, _) |
            &vir::Stmt::Assert(_, _) |
            &vir::Stmt::MethodCall(_, _, _) |
            &vir::Stmt::Assign(_, _, _) |
            &vir::Stmt::Fold(_, _, _) |
            &vir::Stmt::Unfold(_, _, _) |
            &vir::Stmt::Obtain(_) |
            &vir::Stmt::Havoc |
            &vir::Stmt::BeginFrame |
            &vir::Stmt::EndFrame |
            &vir::Stmt::TransferPerm(_, _) |
            &vir::Stmt::ExpireBorrowsIf(_, _, _) |
            &vir::Stmt::StopExpiringLoans |
            &vir::Stmt::PackageMagicWand(_, _, _, _) |
            &vir::Stmt::ApplyMagicWand(_, _) => HashSet::new(),

            &vir::Stmt::WeakObtain(ref expr) => expr.get_required_permissions(predicates),
        }
    }
}

impl RequiredPermissionsGetter for vir::Expr {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<Perm> {
        match self {
            vir::Expr::Const(_) => HashSet::new(),

            vir::Expr::Unfolding(_, args, expr, frac) => {
                assert_eq!(args.len(), 1);
                let arg_place = &args[0].clone().as_place().unwrap();

                // We want to temporarly unfold arg_place
                let predicate_name = arg_place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: HashSet<Perm> = predicate.get_permissions().into_iter()
                    .map( |aop| aop.map_place( |p|
                        p.replace_prefix(&pred_self_place, arg_place.clone())
                    )).collect();

                // Simulate temporary unfolding of `place`
                let expr_req_places = expr.get_required_permissions(predicates);
                let mut req_places: HashSet<_> = difference(&expr_req_places, &places_in_pred);
                req_places.insert(Pred(arg_place.clone(), Frac::one()));
                req_places.into_iter().map(|p| p * frac).collect()
            }

            vir::Expr::LabelledOld(ref label, expr) => {
                let perms = expr.get_required_permissions(predicates);
                perms.into_iter().map(|p| p.old(label)).collect()
            }

            vir::Expr::PredicateAccessPredicate(_, args, _) => {
                assert_eq!(args.len(), 1);
                // FIXME: Don't use full permissions (why?)
                let epsilon = Frac::new(1, 1000);
                match args[0] {
                    vir::Expr::Place(ref place) => {
                        vec![Pred(place.clone(), epsilon), Acc(place.clone(), epsilon)].into_iter().collect()
                    }

                    vir::Expr::LabelledOld(ref label, box vir::Expr::Place(ref place)) => {
                        vec![Pred(place.clone().old(label), epsilon), Acc(place.clone().old(label), epsilon)].into_iter().collect()
                    }

                    _ => unreachable!(),
                }
            }

            vir::Expr::FieldAccessPredicate(expr, frac) => {
                expr.get_required_permissions(predicates).into_iter().map(|p| p * frac).collect()
            }

            vir::Expr::UnaryOp(_, expr) => expr.get_required_permissions(predicates),

            vir::Expr::BinOp(_, box left, box right) => vec![left, right].get_required_permissions(predicates),

            vir::Expr::Cond(box guard, box left, box right) => vec![guard, left, right].get_required_permissions(predicates),

            vir::Expr::ForAll(vars, triggers, box body) => {
                assert!(vars.iter().all(|var| !var.typ.is_ref()));

                let vars_places: HashSet<_> = vars
                    .iter()
                    .map(|var| Acc(vir::Place::Base(var.clone()), Frac::one()))
                    .collect();
                body.get_required_permissions(predicates).difference(&vars_places).cloned().collect()
            }

            vir::Expr::Place(place) => {
                // FIXME: Don't use full permissions
                let epsilon = Frac::new(1, 1000);
                Some(Acc(place.clone(), epsilon)).into_iter().collect()
            },

            vir::Expr::MagicWand(ref lhs, ref _rhs) => {
                // Not exactly Viper's semantics
                HashSet::new()
            }

            vir::Expr::FuncApp(ref name, ref args, ..) => {
                // If the argument is a place to a reference, ask for the full permission on it
                args.iter().map(|a| {
                    match a {
                        vir::Expr::Place(ref place) |
                        vir::Expr::LabelledOld(_, box vir::Expr::Place(ref place)) if place.get_type().is_ref() =>
                            vir::Expr::PredicateAccessPredicate(
                                place.get_type().to_string(),
                                vec![ place.clone().into() ],
                                vir::Frac::one(),
                            ).into(),

                        _ => {
                            a.clone()
                        }
                    }
                }).collect::<Vec<_>>().get_required_permissions(predicates)
            }
        }
    }
}

impl vir::Expr {
    /// Returns the permissions that must be inhaled/exhaled in a `inhale/exhale expr` statement
    /// This must be a subset of `get_required_permissions`
    pub fn get_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<Perm> {
        trace!("get_permissions {}", self);
        match self {
            vir::Expr::Const(_) |
            vir::Expr::Place(_) |
            vir::Expr::LabelledOld(_, _) |
            vir::Expr::FuncApp(..)=> HashSet::new(),

            vir::Expr::Unfolding(_, args, expr, frac) => {
                assert_eq!(args.len(), 1);
                let arg_place = &args[0].clone().as_place().unwrap();

                // We want to temporarly unfold arg_place
                let predicate_name = arg_place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: HashSet<Perm> = predicate.get_permissions().into_iter()
                    .map(
                        |aop| {
                            aop.map_place( |p|
                                p.replace_prefix(&pred_self_place, arg_place.clone())
                            ) * frac
                        }
                    ).collect();

                // Simulate temporary unfolding of `place`
                let expr_access_places = expr.get_permissions(predicates);

                // inhaled = inhaled in body - unfolding
                difference(&expr_access_places, &places_in_pred)
            }

            vir::Expr::UnaryOp(_, ref expr) => expr.get_permissions(predicates),

            vir::Expr::BinOp(_, box left, box right) => {
                union(
                    &left.get_permissions(predicates),
                    &right.get_permissions(predicates)
                )
            },

            vir::Expr::Cond(box guard, box left, box right) => {
                union3(
                    &guard.get_permissions(predicates),
                    &left.get_permissions(predicates),
                    &right.get_permissions(predicates)
                )
            },

            vir::Expr::ForAll(vars, triggers, box body) => {
                assert!(vars.iter().all(|var| !var.typ.is_ref()));
                let vars_places: HashSet<Perm> = vars
                    .iter()
                    .map(|var| Acc(vir::Place::Base(var.clone()), Frac::one()))
                    .collect();
                difference(&body.get_permissions(predicates), &vars_places)
            }

            vir::Expr::PredicateAccessPredicate(_, ref args, frac) => {
                assert_eq!(args.len(), 1);

                /*fn extract_place(expr: &vir::Expr) -> Option<vir::Place> {
                    match expr {
                        &vir::Expr::Place(ref place) => Some(
                            place.clone()
                        ),

                        &vir::Expr::LabelledOld(ref label, box ref expr) => {
                            extract_place(expr).map(
                                |p| Place::old(
                                    p.get_place().clone(),
                                    p.get_label().unwrap_or(label).clone()
                                )
                            )
                        }

                        _ => None
                    }
                }*/

                let opt_perm = match args[0] {
                    vir::Expr::Place(ref place) => Some(
                        Perm::Pred(place.clone(), *frac)
                    ),

                    vir::Expr::LabelledOld(ref label, box vir::Expr::Place(ref place)) => Some(
                        Perm::Pred(place.clone().old(label), *frac)
                    ),

                    ref x => {
                        debug!("Ignore permissions for {}", x);
                        None
                    }
                };

                opt_perm.into_iter().collect()
            }

            vir::Expr::FieldAccessPredicate(ref expr, frac) => {
                // In Prusti we assume to have only places here
                let perm = match expr {
                    box vir::Expr::Place(ref place) => {
                        Acc(place.clone(), *frac)
                    }

                    box vir::Expr::LabelledOld(ref label, box vir::Expr::Place(ref place)) => {
                        Perm::Pred(place.clone().old(label), *frac)
                    }

                    _ => unreachable!()
                };
                Some(perm).into_iter().collect()
            }

            vir::Expr::MagicWand(ref lhs, ref _rhs) => {
                // We don't track magic wands precisely
                HashSet::new()
            }
        }
    }
}

impl vir::Predicate {
    /// Returns the permissions that must be added/removed in a `fold/unfold pred` statement
    pub fn get_permissions(&self) -> HashSet<Perm> {
        match self.body {
            Some(ref body) => {
                // A predicate body should not contain unfolding expression
                let predicates = HashMap::new();
                body.get_permissions(&predicates)
            },
            None => HashSet::new()
        }
    }
}
