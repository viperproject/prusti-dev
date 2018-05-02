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

            &vir::Stmt::Inhale(ref expr) => expr.get_required_places(),

            &vir::Stmt::Exhale(ref expr, _) => expr.get_required_places(),

            &vir::Stmt::Assert(ref expr, _) => expr.get_required_places(),

            &vir::Stmt::MethodCall(_, ref args, _) => args.get_required_places(),

            &vir::Stmt::Assign(_, ref expr) => expr.get_required_places()
        }
    }
}

impl RequiredPlacesGetter for vir::Expr {
    fn get_required_places(&self) -> HashSet<vir::Place> {
        match self {
            vir::Expr::Const(_) => HashSet::new(),

            vir::Expr::Place(place) => HashSet::from_iter(Some(place.clone()).into_iter()),

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
