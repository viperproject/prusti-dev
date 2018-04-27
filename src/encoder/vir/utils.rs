// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various utility methods for working with VIL.

use encoder::vir;

pub trait ExprIterator {
    /// Conjoin a sequence of expressions into a single expression.
    /// Returns true if the sequence has no elements.
    fn conjoin(&mut self) -> vir::Expr;
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
}
