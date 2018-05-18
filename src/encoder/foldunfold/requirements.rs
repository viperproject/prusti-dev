// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashSet;
use encoder::vir;
use std::iter::FromIterator;
use encoder::foldunfold::acc_or_pred::*;
use encoder::foldunfold::acc_or_pred::AccOrPred::*;

pub trait RequiredPlacesGetter {
    fn get_required_places(&self) -> HashSet<AccOrPred>;
}

impl<'a, 'b, A: RequiredPlacesGetter, B: RequiredPlacesGetter> RequiredPlacesGetter for (&'a A, &'b B) {
    fn get_required_places(&self) -> HashSet<AccOrPred> {
        self.0.get_required_places().union(
            &self.1.get_required_places()
        ).cloned().collect()
    }
}

impl<A: RequiredPlacesGetter> RequiredPlacesGetter for Vec<A> {
    fn get_required_places(&self) -> HashSet<AccOrPred> {
        self.iter().fold(
            HashSet::new(),
            |res, x| res.union(&x.get_required_places()).cloned().collect()
        )
    }
}

impl RequiredPlacesGetter for vir::Stmt {
    fn get_required_places(&self) -> HashSet<AccOrPred> {
        match self {
            &vir::Stmt::Comment(_) |
            &vir::Stmt::Label(_) |
            &vir::Stmt::New(_, _) => HashSet::new(),

            &vir::Stmt::Inhale(ref expr) => {
                // footprint = used - inhaled
                expr.get_required_places().difference(&expr.get_access_places()).cloned().collect()
            },

            &vir::Stmt::Exhale(ref expr, _) => expr.get_required_places(),

            &vir::Stmt::Assert(ref expr, _) => expr.get_required_places(),

            &vir::Stmt::MethodCall(_, ref args, ref vars) => {
                // Preconditions and postconditions are empty
                assert!(args.is_empty());
                HashSet::from_iter(vars.iter().cloned().map(|v| Acc(vir::Place::Base(v))))
            },

            &vir::Stmt::Assign(ref lhs_place, ref expr) => {
                let mut res = expr.get_required_places();
                res.insert(Acc(lhs_place.clone()));
                res
            },

            &vir::Stmt::Fold(ref _pred_name, ref args) => {
                assert!(args.len() == 1);
                args[0].get_required_places()
            },

            &vir::Stmt::Unfold(ref _pred_name, ref _args) => {
                unimplemented!()
            },
        }
    }
}

impl RequiredPlacesGetter for vir::Expr {
    /// Returns the permissions required for the expression to be well-defined
    fn get_required_places(&self) -> HashSet<AccOrPred> {
        match self {
            vir::Expr::Const(_) => HashSet::new(),

            vir::Expr::Old(expr) |
            vir::Expr::LabelledOld(expr, _) |
            vir::Expr::PredicateAccessPredicate(expr, _) |
            vir::Expr::FieldAccessPredicate(expr, _) |
            vir::Expr::UnaryOp(_, expr) => expr.get_required_places(),

            vir::Expr::BinOp(_, box left, box right) => (left, right).get_required_places(),

            vir::Expr::Place(place) => {
                Some(Acc(place.clone())).into_iter().collect()
            },

            vir::Expr::PredicateAccess(_, args) => {
                assert_eq!(args.len(), 1);
                match args[0] {
                    vir::Expr::Place(ref place) |
                    vir::Expr::Old(box vir::Expr::Place(ref place)) |
                    vir::Expr::LabelledOld(box vir::Expr::Place(ref place), _) =>
                        Some(Pred(place.clone())).into_iter().collect(),

                    _ => {
                        // Unreachable
                        assert!(false);
                        HashSet::new()
                    }
                }
            },

            vir::Expr::MagicWand(_, _) => unimplemented!("Fold/unfold does not support magic wands (yet)"),
        }
    }
}

impl vir::Expr {
    pub fn get_access_places(&self) -> HashSet<AccOrPred> {
        match self {
            vir::Expr::Const(_) |
            vir::Expr::Place(_) |
            vir::Expr::Old(_) |
            vir::Expr::LabelledOld(_, _) |
            vir::Expr::PredicateAccess(_, _) => HashSet::new(),

            vir::Expr::UnaryOp(_, ref expr) => expr.get_access_places(),

            vir::Expr::BinOp(_, ref left, ref right) => {
                left.get_access_places().union(&right.get_access_places()).cloned().collect()
            },

            vir::Expr::PredicateAccessPredicate(ref expr, _) |
            vir::Expr::FieldAccessPredicate(ref expr, _) => {
                // In Prusti we assume to have only places here
                assert!(
                    match expr {
                        box vir::Expr::Place(_) |
                        box vir::Expr::Old(box vir::Expr::Place(_)) |
                        box vir::Expr::LabelledOld(box vir::Expr::Place(_), _) => true,

                        box vir::Expr::PredicateAccess(_, ref args) |
                        box vir::Expr::Old(box vir::Expr::PredicateAccess(_, ref args)) |
                        box vir::Expr::LabelledOld(box vir::Expr::PredicateAccess(_, ref args), _) => {
                            args.len() == 1 && match args[0] {
                                vir::Expr::Place(_) |
                                vir::Expr::Old(box vir::Expr::Place(_)) |
                                vir::Expr::LabelledOld(box vir::Expr::Place(_), _) => true,

                                _ => false
                            }
                        },

                        _ => false
                    },
                    "Expr {:?}",
                    expr
                );
                expr.get_required_places()
            },

            vir::Expr::MagicWand(_, _) => unimplemented!(),
        }
    }
}


impl vir::Predicate {
    pub fn get_contained_places(&self) -> HashSet<AccOrPred> {
        match self.body {
            Some(ref body) => body.get_access_places(),
            None => HashSet::new()
        }
    }
}
