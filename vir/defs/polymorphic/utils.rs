// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Various utility methods for working with VIR.

use crate::polymorphic::{
    self, ast::*, cfg, CfgMethod, ExprFolder, ExprWalker, FallibleStmtFolder, Function, StmtFolder,
    StmtWalker,
};

/// Substitute (map) expressions in a statement
impl Stmt {
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

/// Substitute (map) old expressions in an expression
impl Expr {
    #[allow(dead_code)]
    pub fn map_old_expr<F>(self, substitutor: F) -> Self
    where
        F: Fn(&str, Expr) -> Expr,
    {
        trace!("Expr::map_old_expr {}", self);
        struct ExprOldExprSubstitutor<T>
        where
            T: Fn(&str, Expr) -> Expr,
        {
            substitutor: T,
        }
        impl<T> ExprFolder for ExprOldExprSubstitutor<T>
        where
            T: Fn(&str, Expr) -> Expr,
        {
            fn fold_labelled_old(
                &mut self,
                LabelledOld {
                    label,
                    base,
                    position,
                }: LabelledOld,
            ) -> Expr {
                (self.substitutor)(&label, *base).set_pos(position)
            }
        }
        ExprOldExprSubstitutor { substitutor }.fold(self)
    }
}

/// In an expression, substitute labels of old expressions
impl Expr {
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
            fn fold_labelled_old(
                &mut self,
                LabelledOld {
                    label,
                    base,
                    position,
                }: LabelledOld,
            ) -> Expr {
                Expr::LabelledOld(LabelledOld {
                    label: (self.substitutor)(label),
                    base,
                    position,
                })
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
            for (ref expr, _) in conditional_targets {
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

/// Walks all Statements and Expressions in the provided methods
pub fn fallible_walk_methods<E>(
    methods: &[CfgMethod],
    walker: &mut (impl FallibleStmtWalker<Error = E> + FallibleExprWalker<Error = E>),
) -> Result<(), E> {
    for method in methods {
        fallible_walk_method(method, walker)?;
    }
    Ok(())
}

pub fn fallible_walk_method<E>(
    method: &CfgMethod,
    walker: &mut (impl FallibleStmtWalker<Error = E> + FallibleExprWalker<Error = E>),
) -> Result<(), E> {
    method.fallible_walk_statements(|stmt| FallibleStmtWalker::fallible_walk(walker, stmt))?;
    method.fallible_walk_successors(|successor| {
        match successor {
            cfg::Successor::Undefined | cfg::Successor::Return | cfg::Successor::Goto(_) => {}
            cfg::Successor::GotoSwitch(conditional_targets, _) => {
                for (ref expr, _) in conditional_targets {
                    FallibleExprWalker::fallible_walk(walker, expr)?;
                }
            }
        }
        Ok(())
    })?;
    Ok(())
}
