// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashSet;
use encoder::vir;
use std::iter::FromIterator;

pub trait RequiredPlacesGetter {
    fn get_required_places(&self) -> HashSet<vir::Place>;
}

impl<'a, 'b, A: RequiredPlacesGetter, B: RequiredPlacesGetter> RequiredPlacesGetter for (&'a A, &'b B) {
    fn get_required_places(&self) -> HashSet<vir::Place> {
        self.0.get_required_places().union(
            &self.1.get_required_places()
        ).cloned().collect()
    }
}

impl<A: RequiredPlacesGetter> RequiredPlacesGetter for Vec<A> {
    fn get_required_places(&self) -> HashSet<vir::Place> {
        self.iter().fold(
            HashSet::new(),
            |res, x| res.union(&x.get_required_places()).cloned().collect()
        )
    }
}

impl RequiredPlacesGetter for vir::Stmt {
    fn get_required_places(&self) -> HashSet<vir::Place> {
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
                HashSet::from_iter(vars.iter().cloned().map(|v| vir::Place::Base(v)))
            },

            &vir::Stmt::Assign(ref lhs_place, ref expr) => {
                let mut res = expr.get_required_places();
                res.insert(lhs_place.clone());
                res
            },

            &vir::Stmt::Fold(ref pred_name, ref args) => {
                assert!(args.len() == 1);
                args[0].get_required_places()
            },

            &vir::Stmt::Unfold(ref pred_name, ref args) => {
                unimplemented!()
            },
        }
    }
}

impl vir::Stmt {
    pub fn get_resulting_places(&self, places: &HashSet<vir::Place>) -> HashSet<vir::Place> {
        assert!(
            self.get_required_places().is_subset(places),
            "With stmt '{:?}'\nget_required_places: {:?}\nis not subset of places: {:?}",
            &self,
            self.get_required_places().iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", "),
            places.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
        );
        match self {
            &vir::Stmt::Comment(_) |
            &vir::Stmt::Label(_) |
            &vir::Stmt::Inhale(_) |
            &vir::Stmt::Assert(_, _) => places.clone(),

            &vir::Stmt::New(ref var, ref fields) => {
                let mut res: HashSet<vir::Place> = places.iter()
                    .filter(|p| p.base() != var)
                    .cloned()
                    .collect();
                for field in fields {
                    res.insert(vir::Place::Base(var.clone()).access(field.clone()));
                }
                res
            },

            &vir::Stmt::Exhale(ref expr, _) => {
                places.difference(&expr.get_access_places()).cloned().collect()
            },

            &vir::Stmt::MethodCall(_, _, ref vars) => {
                // Preconditions and postconditions are empty
                let mut res: HashSet<vir::Place> = places.iter()
                    .filter(|p| !vars.contains(p.base()) || (p.is_base() && vars.contains(p.base())))
                    .cloned()
                    .collect();
                res
            },

            &vir::Stmt::Assign(ref lhs_place, ref rhs) => {
                // First of all, remove places that will not have a name
                let mut final_places: HashSet<vir::Place> = places.iter()
                    .filter(|p| !p.has_prefix(&lhs_place) || p == &lhs_place)
                    .cloned()
                    .collect();
                // Then, in case of aliasing, add new places
                match rhs {
                    &vir::Expr::Place(ref rhs_place) if rhs_place.get_type().is_ref() => {
                        // An alias is created, with new places
                        let new_places = places.iter()
                            .filter(|p| p.has_prefix(&rhs_place) && p != &rhs_place)
                            .cloned()
                            .map(|p| p.replace_prefix(&rhs_place, lhs_place.clone()));
                        for place in new_places {
                            final_places.insert(place);
                        }
                    },
                    _ => {}
                }
                final_places
            },

            &vir::Stmt::Fold(ref pred_name, ref args) => {
                unimplemented!()
            },

            &vir::Stmt::Unfold(ref pred_name, ref args) => {
                unimplemented!()
            },
        }
    }
}

impl RequiredPlacesGetter for vir::Expr {
    fn get_required_places(&self) -> HashSet<vir::Place> {
        match self {
            vir::Expr::Const(_) => HashSet::new(),

            vir::Expr::Place(place) => {
                Some(place.clone()).into_iter().collect()
            },

            vir::Expr::Old(expr) |
            vir::Expr::LabelledOld(expr, _) |
            vir::Expr::PredicateAccessPredicate(expr, _) |
            vir::Expr::FieldAccessPredicate(expr, _) |
            vir::Expr::UnaryOp(_, expr) => expr.get_required_places(),

            vir::Expr::MagicWand(_, _) => unimplemented!(),

            vir::Expr::PredicateAccess(_, args) => args.get_required_places(),

            vir::Expr::BinOp(_, box left, box right) => (left, right).get_required_places(),
        }
    }
}

impl vir::Expr {
    fn get_access_places(&self) -> HashSet<vir::Place> {
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
    pub fn get_contained_places(&self) -> HashSet<vir::Place> {
        match self.body {
            Some(ref body) => body.get_access_places(),
            None => HashSet::new()
        }
    }
}
