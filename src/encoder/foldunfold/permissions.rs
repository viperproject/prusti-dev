// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::foldunfold::perm::*;
use encoder::foldunfold::perm::Perm::*;
use encoder::vir;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::FromIterator;

pub trait RequiredPermissionsGetter {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<LabelledPerm>;
}

impl<'a, A: RequiredPermissionsGetter> RequiredPermissionsGetter for Vec<&'a A> {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<LabelledPerm> {
        self.iter().fold(
            HashSet::new(),
            |res, x| res.union(&x.get_required_permissions(predicates)).cloned().collect()
        )
    }
}

impl RequiredPermissionsGetter for Vec<vir::Expr> {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<LabelledPerm> {
        self.iter().fold(
            HashSet::new(),
            |res, x| res.union(&x.get_required_permissions(predicates)).cloned().collect()
        )
    }
}

impl RequiredPermissionsGetter for vir::Stmt {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<LabelledPerm> {
        match self {
            &vir::Stmt::Comment(_) |
            &vir::Stmt::Label(_) => HashSet::new(),

            &vir::Stmt::Inhale(ref expr) => {
                // footprint = used - inhaled
                expr.get_required_permissions(predicates).difference(
                    &expr.get_permissions(predicates).into_iter().map(|p| LabelledPerm::curr(p)).collect()
                ).cloned().collect()
            },

            &vir::Stmt::Exhale(ref expr, _) => expr.get_required_permissions(predicates),

            &vir::Stmt::Assert(ref expr, _) => expr.get_required_permissions(predicates),

            &vir::Stmt::MethodCall(_, ref args, ref vars) => {
                // Preconditions and postconditions are empty
                assert!(args.is_empty());
                HashSet::from_iter(vars.iter().cloned().map(|v| LabelledPerm::curr(Acc(vir::Place::Base(v)))))
            },

            &vir::Stmt::Assign(ref lhs_place, ref expr, kind) => {
                let mut res = expr.get_required_permissions(predicates);
                res.insert(LabelledPerm::curr(Acc(lhs_place.clone())));
                res
            },

            &vir::Stmt::Fold(ref _pred_name, ref args) => {
                assert_eq!(args.len(), 1);
                let arg_place = &args[0].clone().as_place().unwrap();

                // We want to temporarly unfold arg_place
                let predicate_name = arg_place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: HashSet<Perm> = predicate.get_permissions().into_iter()
                    .map( |aop| aop.map( |p|
                        p.replace_prefix(&pred_self_place, arg_place.clone())
                    )).collect();

                places_in_pred.into_iter().map(|p| LabelledPerm::curr(p)).collect()
            },

            &vir::Stmt::Unfold(ref _pred_name, ref args) => {
                assert_eq!(args.len(), 1);
                args[0].get_required_permissions(predicates)
            },

            &vir::Stmt::Obtain(ref expr) => expr.get_required_permissions(predicates),
        }
    }
}

impl RequiredPermissionsGetter for vir::Expr {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_permissions(&self, predicates: &HashMap<String, vir::Predicate>) -> HashSet<LabelledPerm> {
        match self {
            vir::Expr::Const(_) => HashSet::new(),

            vir::Expr::Unfolding(_, args, expr) => {
                assert_eq!(args.len(), 1);
                let arg_place = &args[0].clone().as_place().unwrap();

                // We want to temporarly unfold arg_place
                let predicate_name = arg_place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: HashSet<Perm> = predicate.get_permissions().into_iter()
                    .map( |aop| aop.map( |p|
                        p.replace_prefix(&pred_self_place, arg_place.clone())
                    )).collect();

                // Simulate temporary unfolding of `place`
                let expr_req_places = expr.get_required_permissions(predicates);
                let mut req_places: HashSet<_> = expr_req_places.difference(
                    &places_in_pred.into_iter().map(|p| LabelledPerm::curr(p)).collect()
                ).cloned().collect();
                req_places.insert(LabelledPerm::curr(Pred(arg_place.clone())));
                req_places
            }

            vir::Expr::LabelledOld(ref label, expr) => {
                let perms = expr.get_required_permissions(predicates);
                perms.into_iter().map(|p| match p {
                    LabelledPerm::Curr(perm) => LabelledPerm::old(label, perm),
                    x => x
                }).collect()
            }

            vir::Expr::PredicateAccessPredicate(expr, _) |
            vir::Expr::FieldAccessPredicate(expr, _) |
            vir::Expr::UnaryOp(_, expr) => expr.get_required_permissions(predicates),

            vir::Expr::BinOp(_, box left, box right) => vec![left, right].get_required_permissions(predicates),

            vir::Expr::Cond(box guard, box left, box right) => vec![guard, left, right].get_required_permissions(predicates),

            vir::Expr::ForAll(vars, triggers, box body) => {
                assert!(vars.iter().all(|var| !var.typ.is_ref()));

                let vars_places: HashSet<_> = vars
                    .iter()
                    .map(|var| LabelledPerm::curr(Acc(vir::Place::Base(var.clone()))))
                    .collect();
                body.get_required_permissions(predicates).difference(&vars_places).cloned().collect()
            }

            vir::Expr::Place(place) => {
                if !place.is_base() {
                    Some(LabelledPerm::curr(Acc(place.clone()))).into_iter().collect()
                } else {
                    None.into_iter().collect()
                }
            },

            vir::Expr::PredicateAccess(_, args) => {
                assert_eq!(args.len(), 1);
                match args[0] {
                    vir::Expr::Place(ref place) =>
                        vec![LabelledPerm::curr(Pred(place.clone())), LabelledPerm::curr(Acc(place.clone()))].into_iter().collect(),

                    vir::Expr::LabelledOld(ref label, box vir::Expr::Place(ref place)) =>
                        vec![LabelledPerm::old(label, Pred(place.clone())), LabelledPerm::old(label, Acc(place.clone()))].into_iter().collect(),

                    _ => {
                        // Unreachable
                        assert!(false);
                        HashSet::new()
                    }
                }
            },

            vir::Expr::MagicWand(_, _) => unimplemented!("Fold/unfold does not support magic wands (yet)"),

            vir::Expr::FuncApp(ref name, ref args, ..) => {
                // If the argument is a place to a reference, ask for the full permission on it
                args.iter().map(|a| {
                    match a {
                        vir::Expr::Place(ref place) |
                        vir::Expr::LabelledOld(_, box vir::Expr::Place(ref place)) if place.get_type().is_ref() =>
                            vir::Expr::PredicateAccessPredicate(
                                box vir::Expr::PredicateAccess(
                                    place.get_type().to_string(),
                                    vec![ place.clone().into() ]
                                ),
                                vir::Perm::full()
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
            vir::Expr::PredicateAccess(_, _) |
            vir::Expr::FuncApp(..)=> HashSet::new(),

            vir::Expr::Unfolding(_, args, expr) => {
                assert_eq!(args.len(), 1);
                let arg_place = &args[0].clone().as_place().unwrap();

                // We want to temporarly unfold arg_place
                let predicate_name = arg_place.typed_ref_name().unwrap();
                let predicate = predicates.get(&predicate_name).unwrap();

                let pred_self_place: vir::Place = predicate.args[0].clone().into();
                let places_in_pred: HashSet<Perm> = predicate.get_permissions().into_iter()
                    .map( |aop| aop.map( |p|
                        p.replace_prefix(&pred_self_place, arg_place.clone())
                    )).collect();

                // Simulate temporary unfolding of `place`
                let expr_access_places = expr.get_permissions(predicates);
                let access_places: HashSet<_> = expr_access_places.difference(&places_in_pred).cloned().collect();
                access_places
            }

            vir::Expr::UnaryOp(_, ref expr) => expr.get_permissions(predicates),

            vir::Expr::BinOp(_, box left, box right) => {
                left.get_permissions(predicates).union(&right.get_permissions(predicates)).cloned().collect()
            },

            vir::Expr::Cond(box guard, box left, box right) => {
                let partial_res: HashSet<_> = guard.get_permissions(predicates).union(&left.get_permissions(predicates)).cloned().collect();
                partial_res.union(&right.get_permissions(predicates)).cloned().collect()
            },

            vir::Expr::ForAll(vars, triggers, box body) => {
                assert!(vars.iter().all(|var| !var.typ.is_ref()));

                let vars_places: HashSet<_> = vars
                    .iter()
                    .map(|var| Acc(vir::Place::Base(var.clone())))
                    .collect();
                body.get_permissions(predicates).difference(&vars_places).cloned().collect()
            }

            vir::Expr::PredicateAccessPredicate(ref expr, _) |
            vir::Expr::FieldAccessPredicate(ref expr, _) => {
                // In Prusti we assume to have only places here
                let opt_perm = match expr {
                    box vir::Expr::Place(ref place) => Some(Perm::Acc(place.clone())),

                    box vir::Expr::PredicateAccess(_, ref args) => {
                        assert_eq!(args.len(), 1);
                        match args[0] {
                            vir::Expr::Place(ref place) => Some(Perm::Pred(place.clone())),

                            vir::Expr::LabelledOld(..) => None,

                            _ => unreachable!()
                        }
                    },

                    _ => unreachable!()
                };
                opt_perm.into_iter().collect()
            },

            vir::Expr::MagicWand(_, _) => unimplemented!(),
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
