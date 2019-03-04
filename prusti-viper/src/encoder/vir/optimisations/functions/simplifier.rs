// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Function simplifier that simplifies expressions.

use std::mem;
use super::super::super::ast;

/// Simplify functions by doing some constant evaluation.
pub fn simplify(function: &mut ast::Function) {
    if let Some(ref mut body) = function.body {
        body.simplify();
    }
    debug!("Simplified function: {}", function);
}

trait Simplifier {
    /// Simplify by doing constant evaluation.
    fn simplify(&mut self);
}

impl Simplifier for ast::Expr {

    fn simplify(&mut self) {
        match self {
            ast::Expr::BinOp(_, box subexpr1, box subexpr2) => {
                subexpr1.simplify();
                subexpr2.simplify();
            },
            _ => {},
        }
         match self {
            ast::Expr::BinOp(ast::BinOpKind::And,
                             box ast::Expr::Const(ast::Const::Bool(b1)),
                             box ast::Expr::Const(ast::Const::Bool(b2))) => {
                let mut new_value = ast::Expr::Const(ast::Const::Bool(*b1 && *b2));
                mem::swap(self, &mut new_value);
            },
            _ => {},
        }
    }

}
