// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various utility methods for working with VIR.

use encoder::vir;
use encoder::vir::ExprFolder;
use encoder::vir::ExprWalker;
use encoder::vir::StmtFolder;

/// Substitute (map) expressions in a statement
impl vir::Stmt {
    pub fn map_expr<F>(self, substitutor: F) -> Self where F: Fn(vir::Expr) -> vir::Expr {
        trace!("Stmt::map_expr {}", self);
        struct StmtExprSubstitutor<T> where T: Fn(vir::Expr) -> vir::Expr {
            substitutor: T,
        }
        impl<T> vir::StmtFolder for StmtExprSubstitutor<T> where T: Fn(vir::Expr) -> vir::Expr {
            fn fold_expr(&mut self, e: vir::Expr) -> vir::Expr {
                (self.substitutor)(e)
            }
        }
        StmtExprSubstitutor {
            substitutor,
        }.fold(self)
    }
}

/// Substitute (map) old expressions in an expression
impl vir::Expr {
    pub fn map_old_expr<F>(self, substitutor: F) -> Self where F: Fn(&str, vir::Expr) -> vir::Expr {
        trace!("Expr::map_old_expr {}", self);
        struct ExprOldExprSubstitutor<T> where T: Fn(&str, vir::Expr) -> vir::Expr {
            substitutor: T,
        }
        impl<T> vir::ExprFolder for ExprOldExprSubstitutor<T> where T: Fn(&str, vir::Expr) -> vir::Expr {
            fn fold_labelled_old(&mut self, x: String, y: Box<vir::Expr>, p: vir::Position) -> vir::Expr {
                (self.substitutor)(&x, *y).set_pos(p)
            }
        }
        ExprOldExprSubstitutor {
            substitutor,
        }.fold(self)
    }
}

/// In an expression, substitute labels of old expressions
impl vir::Expr {
    pub fn map_old_expr_label<F>(self, substitutor: F) -> Self where F: Fn(String) -> String {
        trace!("Expr::map_old_expr_label {}", self);
        struct ExprLabelSubstitutor<T> where T: Fn(String) -> String {
            substitutor: T,
        }
        impl<T> vir::ExprFolder for ExprLabelSubstitutor<T> where T: Fn(String) -> String {
            fn fold_labelled_old(&mut self, x: String, y: Box<vir::Expr>, p: vir::Position) -> vir::Expr {
                vir::Expr::LabelledOld((self.substitutor)(x), y, p)
            }
        }
        ExprLabelSubstitutor {
            substitutor,
        }.fold(self)
    }
}
