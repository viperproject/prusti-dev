// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Function simplifier that simplifies expressions.

use super::super::super::ast::{self, ExprFolder};

pub trait Simplifier {
    /// Simplify by doing constant evaluation.
    fn simplify(self) -> Self;
}

impl Simplifier for ast::Function {
    /// Simplify functions in a way that tries to work-around regressions caused by
    /// https://bitbucket.org/viperproject/silicon/issues/387/incompleteness-in-morecompleteexhale
    fn simplify(mut self) -> Self {
        trace!("[enter] simplify = {}", self);
        let new_body = self.body.map(|b| b.simplify());
        self.body = new_body;
        trace!("[exit] simplify = {}", self);
        self
    }
}

impl Simplifier for ast::Expr {
    fn simplify(self) -> Self {
        let mut folder = ExprSimplifier {};
        folder.fold(self)
    }
}

struct ExprSimplifier {}

impl ExprSimplifier {
    fn apply_rules(&self, e: ast::Expr) -> ast::Expr {
        trace!("[enter] apply_rules={}", e);
        let result = match e {
            ast::Expr::UnaryOp(
                ast::UnaryOpKind::Not,
                box ast::Expr::Const(ast::Const::Bool(b), _),
                pos,
            ) => {
                ast::Expr::Const(ast::Const::Bool(!b), pos)
            },
            ast::Expr::UnaryOp(
                ast::UnaryOpKind::Not,
                box ast::Expr::BinOp(ast::BinOpKind::EqCmp, box left, box right, _),
                pos,
            ) => {
                ast::Expr::BinOp(ast::BinOpKind::NeCmp, box left, box right, pos)
            },
            ast::Expr::BinOp(
                ast::BinOpKind::And,
                box ast::Expr::Const(ast::Const::Bool(b1), _),
                box ast::Expr::Const(ast::Const::Bool(b2), _),
                pos,
            ) => {
                ast::Expr::Const(ast::Const::Bool(b1 && b2), pos)
            },
            ast::Expr::BinOp(
                ast::BinOpKind::And,
                box ast::Expr::Const(ast::Const::Bool(b), _),
                box conjunct,
                pos,
            ) |
            ast::Expr::BinOp(
                ast::BinOpKind::And,
                box conjunct,
                box ast::Expr::Const(ast::Const::Bool(b), _),
                pos,
            ) => {
                if b {
                    conjunct
                } else {
                    ast::Expr::Const(ast::Const::Bool(false.into()), pos)
                }
            },
            ast::Expr::BinOp(
                ast::BinOpKind::Or,
                box ast::Expr::Const(ast::Const::Bool(b), _),
                box disjunct,
                pos,
            ) |
            ast::Expr::BinOp(
                ast::BinOpKind::Or,
                box disjunct,
                box ast::Expr::Const(ast::Const::Bool(b), _),
                pos,
            ) => {
                if b {
                    ast::Expr::Const(ast::Const::Bool(true.into()), pos)
                } else {
                    disjunct
                }
            },
            ast::Expr::BinOp(
                ast::BinOpKind::Implies,
                guard,
                box ast::Expr::Const(ast::Const::Bool(b), _),
                pos,
            ) => {
                if b {
                    ast::Expr::Const(ast::Const::Bool(true.into()), pos)
                } else {
                    ast::Expr::UnaryOp(
                        ast::UnaryOpKind::Not,
                        guard,
                        pos,
                    )
                }
            },
            ast::Expr::BinOp(
                ast::BinOpKind::Implies,
                box ast::Expr::Const(ast::Const::Bool(b), _),
                box body,
                pos,
            ) => {
                if b {
                    body
                } else {
                    ast::Expr::Const(ast::Const::Bool(true.into()), pos)
                }
            },
            ast::Expr::BinOp(ast::BinOpKind::And, box op1, box op2, pos) => {
                ast::Expr::BinOp(
                    ast::BinOpKind::And,
                    box self.apply_rules(op1),
                    box self.apply_rules(op2),
                    pos,
                )
            },
            r => r,
        };
        trace!("[exit] apply_rules={}", result);
        result
    }
}

impl ExprFolder for ExprSimplifier {
    fn fold(&mut self, e: ast::Expr) -> ast::Expr {
        let folded_expr = ast::default_fold_expr(self, e);
        self.apply_rules(folded_expr)
    }
    fn fold_cond(
        &mut self,
        guard: Box<ast::Expr>,
        then_expr: Box<ast::Expr>,
        else_expr: Box<ast::Expr>,
        pos: ast::Position
    ) -> ast::Expr {
        let simplified_guard = self.fold_boxed(guard);
        let simplified_then = self.fold_boxed(then_expr);
        let simplified_else = self.fold_boxed(else_expr);
        let result = if simplified_then.is_bool() || simplified_else.is_bool() {
            ast::Expr::BinOp(
                ast::BinOpKind::And,
                box ast::Expr::BinOp(
                    ast::BinOpKind::Implies,
                    simplified_guard.clone(),
                    simplified_then,
                    pos,
                ),
                box ast::Expr::BinOp(
                    ast::BinOpKind::Implies,
                    box ast::Expr::UnaryOp(
                        ast::UnaryOpKind::Not,
                        simplified_guard,
                        pos,
                    ),
                    simplified_else,
                    pos,
                ),
                pos,
            )
        } else {
            ast::Expr::Cond(simplified_guard, simplified_then, simplified_else, pos)
        };
        self.apply_rules(result)
    }
}
