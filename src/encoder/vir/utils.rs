// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various utility methods for working with VIR.

use encoder::vir;
use encoder::vir::ExprFolder;
use encoder::vir::ExprWalker;
use encoder::vir::StmtFolder;

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

impl vir::Expr {
    pub fn substitute_place_with_place(self, sub_target: &vir::Place, replacement: vir::Place) -> Self {
        trace!("Expr::substitute_place_with_place {}, {}, {}", self, sub_target, replacement);
        ExprSubPlaceSubstitutor {
            sub_target,
            replacement,
        }.fold(self)
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

pub fn substitute_place_in_expr(expr: vir::Expr, sub_target: &vir::Place, replacement: vir::Expr) -> vir::Expr {
    if let vir::Expr::Place(replacement_place) = replacement {
        ExprSubPlaceSubstitutor::substitute(expr, sub_target, replacement_place)
    } else {
        ExprExactPlaceSubstitutor::substitute(expr, sub_target, replacement)
    }
}

impl vir::Expr {
    pub fn substitute_place_with_expr(self, sub_target: &vir::Place, replacement: vir::Expr) -> Self {
        trace!("Expr::substitute_place_with_expr {}, {}, {}", self, sub_target, replacement);
        substitute_place_in_expr(self, sub_target, replacement)
    }
}


/// Substitute (map) expressions in a statement
pub struct StmtExprSubstitutor<F> where F: Fn(vir::Expr) -> vir::Expr {
    substitutor: F,
}

impl<F> vir::StmtFolder for StmtExprSubstitutor<F> where F: Fn(vir::Expr) -> vir::Expr {
    fn fold_expr(&mut self, e: vir::Expr) -> vir::Expr {
        (self.substitutor)(e)
    }
}

impl vir::Stmt {
    pub fn map_expr<F>(self, substitutor: F) -> Self where F: Fn(vir::Expr) -> vir::Expr {
        trace!("Stmt::map_expr {}", self);
        StmtExprSubstitutor {
            substitutor,
        }.fold(self)
    }
}

/// Substitute (map) old expressions in an expression
pub struct ExprOldExprSubstitutor<F> where F: Fn(&str, vir::Expr) -> vir::Expr {
    substitutor: F,
}

impl<F> vir::ExprFolder for ExprOldExprSubstitutor<F> where F: Fn(&str, vir::Expr) -> vir::Expr {
    fn fold_labelled_old(&mut self, x: String, y: Box<vir::Expr>) -> vir::Expr {
        let new_expr = (self.substitutor)(&x, *y);
        vir::Expr::LabelledOld(x, box new_expr)
    }
}

impl vir::Expr {
    pub fn map_old_expr<F>(self, substitutor: F) -> Self where F: Fn(&str, vir::Expr) -> vir::Expr {
        trace!("Expr::map_old_expr {}", self);
        ExprOldExprSubstitutor {
            substitutor,
        }.fold(self)
    }
}
