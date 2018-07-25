// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various utility methods for working with VIR.

use encoder::vir;
use encoder::vir::ExprFolder;
use encoder::vir::ExprWalker;

pub trait ExprIterator {
    /// Conjoin a sequence of expressions into a single expression.
    /// Returns true if the sequence has no elements.
    fn conjoin(&mut self) -> vir::Expr;

    /// Disjoin a sequence of expressions into a single expression.
    /// Returns true if the sequence has no elements.
    fn disjoin(&mut self) -> vir::Expr;
}

impl<T> ExprIterator for T
    where
        T: Iterator<Item = vir::Expr>
{
    fn conjoin(&mut self) -> vir::Expr {
        if let Some(init) = self.next() {
            self.fold(init, |acc, conjunct| vir::Expr::and(acc, conjunct))
        } else {
            true.into()
        }
    }

    fn disjoin(&mut self) -> vir::Expr {
        if let Some(init) = self.next() {
            self.fold(init, |acc, conjunct| vir::Expr::or(acc, conjunct))
        } else {
            true.into()
        }
    }
}

/// In an expression, substitute an exact match of a place with an expression
pub struct ExprExactPlaceSubstitutor<'a> {
    exact_target: &'a vir::Place,
    replacement: vir::Expr,
}

impl<'a> ExprExactPlaceSubstitutor<'a> {
    pub fn substitute(expr: vir::Expr, exact_target: &'a vir::Place, replacement: vir::Expr) -> vir::Expr {
        ExprExactPlaceSubstitutor {
            exact_target,
            replacement,
        }.fold(expr)
    }
}

impl<'a> vir::ExprFolder for ExprExactPlaceSubstitutor<'a> {
    fn fold_place(&mut self, place: vir::Place) -> vir::Expr {
        if &place == self.exact_target {
            self.replacement.clone()
        } else {
            vir::Expr::Place(place)
        }
    }
}

/// In an expression, substitute a prefix of a place with another place
pub struct ExprSubPlaceSubstitutor<'a> {
    sub_target: &'a vir::Place,
    replacement: vir::Place,
}

impl<'a> ExprSubPlaceSubstitutor<'a> {
    pub fn substitute(expr: vir::Expr, sub_target: &'a vir::Place, replacement: vir::Place) -> vir::Expr {
        ExprSubPlaceSubstitutor {
            sub_target,
            replacement,
        }.fold(expr)
    }
}

impl<'a> vir::ExprFolder for ExprSubPlaceSubstitutor<'a> {
    fn fold_place(&mut self, place: vir::Place) -> vir::Expr {
        vir::Expr::Place(place.replace_prefix(self.sub_target, self.replacement.clone()))
    }
}

/// In an expression, find if there is a prefix of a wanted place
pub struct ExprPlaceFinder<'a> {
    sub_target: &'a vir::Place,
    found: bool
}

impl<'a> ExprPlaceFinder<'a> {
    pub fn find(expr: &vir::Expr, sub_target: &'a vir::Place) -> bool {
        let mut finder = ExprPlaceFinder {
            sub_target,
            found: false,
        };
        finder.walk(expr);
        finder.found
    }
}

impl<'a> vir::ExprWalker for ExprPlaceFinder<'a> {
    fn walk_place(&mut self, place: &vir::Place) {
        if place.has_prefix(self.sub_target) {
            self.found = true;
        }
    }
}
