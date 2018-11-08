// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various utility methods for working with VIR.

use encoder::vir;
use encoder::vir::ExprFolder;
use encoder::vir::ExprWalker;
use encoder::vir::StmtFolder;


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
        (self.substitutor)(&x, *y)
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

/// In an expression, substitute labels of old expressions
pub struct ExprLabelSubstitutor<F> where F: Fn(String) -> String {
    substitutor: F,
}

impl<F> vir::ExprFolder for ExprLabelSubstitutor<F> where F: Fn(String) -> String {
    fn fold_labelled_old(&mut self, x: String, y: Box<vir::Expr>) -> vir::Expr {
        vir::Expr::LabelledOld((self.substitutor)(x), y)
    }
}

impl vir::Expr {
    pub fn map_old_expr_label<F>(self, substitutor: F) -> Self where F: Fn(String) -> String {
        trace!("Expr::map_old_expr_label {}", self);
        ExprLabelSubstitutor {
            substitutor,
        }.fold(self)
    }
}