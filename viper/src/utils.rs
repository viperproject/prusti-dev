// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various utility methods for working with Viper.

use crate::ast_factory::{AstFactory, Expr};

pub trait ExprIterator<'v> {
    /// Conjoin a sequence of expressions into a single expression.
    /// Panics if the sequence has no elements.
    fn conjoin(&mut self, ast: &AstFactory<'v>) -> Expr<'v>;

    /// Conjoin a sequence of expressions into a single expression.
    fn conjoin_with_init(&mut self, ast: &AstFactory<'v>, init: Expr<'v>) -> Expr<'v>;
}

impl<'v, T> ExprIterator<'v> for T
where
    T: Iterator<Item = Expr<'v>>,
{
    fn conjoin(&mut self, ast: &AstFactory<'v>) -> Expr<'v> {
        let init = self.next().unwrap();
        self.conjoin_with_init(ast, init)
    }

    fn conjoin_with_init(&mut self, ast: &AstFactory<'v>, init: Expr<'v>) -> Expr<'v> {
        self.fold(init, |acc, conjunct| ast.and(acc, conjunct))
    }
}
