// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various utility methods for working with VIR.

use crate::legacy::{
    self, ast::*, cfg, CfgMethod, ExprFolder, ExprWalker, FallibleStmtFolder, Function, StmtFolder,
    StmtWalker,
};
use log::trace;

/// Substitute (map) expressions in a statement
impl Stmt {
    #[must_use]
    pub fn map_expr<F>(self, substitutor: F) -> Self
    where
        F: Fn(Expr) -> Expr,
    {
        trace!("Stmt::map_expr {}", self);
        struct StmtExprSubstitutor<T>
        where
            T: Fn(Expr) -> Expr,
        {
            substitutor: T,
        }
        impl<T> StmtFolder for StmtExprSubstitutor<T>
        where
            T: Fn(Expr) -> Expr,
        {
            fn fold_expr(&mut self, e: Expr) -> Expr {
                (self.substitutor)(e)
            }
        }
        StmtExprSubstitutor { substitutor }.fold(self)
    }

    pub fn fallible_map_expr<F, E>(self, substitutor: F) -> Result<Self, E>
    where
        F: Fn(Expr) -> Result<Expr, E>,
    {
        trace!("Stmt::fallible_map_expr {}", self);
        struct StmtExprSubstitutor<T, U>
        where
            T: Fn(Expr) -> Result<Expr, U>,
        {
            substitutor: T,
        }
        impl<T, U> FallibleStmtFolder for StmtExprSubstitutor<T, U>
        where
            T: Fn(Expr) -> Result<Expr, U>,
        {
            type Error = U;

            fn fallible_fold_expr(&mut self, e: Expr) -> Result<Expr, U> {
                (self.substitutor)(e)
            }
        }
        StmtExprSubstitutor { substitutor }.fallible_fold(self)
    }
}

/// In an expression, substitute labels of old expressions
impl Expr {
    #[must_use]
    pub fn map_old_expr_label<F>(self, substitutor: F) -> Self
    where
        F: Fn(String) -> String,
    {
        trace!("Expr::map_old_expr_label {}", self);
        struct ExprLabelSubstitutor<T>
        where
            T: Fn(String) -> String,
        {
            substitutor: T,
        }
        impl<T> ExprFolder for ExprLabelSubstitutor<T>
        where
            T: Fn(String) -> String,
        {
            fn fold_labelled_old(&mut self, x: String, y: Box<Expr>, p: Position) -> Expr {
                Expr::LabelledOld((self.substitutor)(x), y, p)
            }
        }
        ExprLabelSubstitutor { substitutor }.fold(self)
    }
}

/// Walks all Statements and Expressions in the provided methods
pub fn walk_methods(methods: &[CfgMethod], walker: &mut (impl StmtWalker + ExprWalker)) {
    for method in methods {
        walk_method(method, walker);
    }
}

pub fn walk_method(method: &CfgMethod, walker: &mut (impl StmtWalker + ExprWalker)) {
    method.walk_statements(|stmt| {
        StmtWalker::walk(walker, stmt);
    });
    method.walk_successors(|successor| match successor {
        cfg::Successor::Undefined | cfg::Successor::Return | cfg::Successor::Goto(_) => {}
        cfg::Successor::GotoSwitch(conditional_targets, _) => {
            for (expr, _) in conditional_targets {
                ExprWalker::walk(walker, expr);
            }
        }
    });
}

/// Walks all Expressions in the provided functions (including pre and post conditions)
pub fn walk_functions(functions: &[Function], walker: &mut impl ExprWalker) {
    for function in functions {
        for e in &function.pres {
            ExprWalker::walk(walker, e);
        }

        for e in &function.posts {
            ExprWalker::walk(walker, e);
        }

        for e in &function.body {
            ExprWalker::walk(walker, e);
        }
    }
}
