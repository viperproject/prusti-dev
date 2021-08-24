// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Function simplifier that simplifies expressions.

use crate::vir::polymorphic_vir::ast::{self, ExprFolder};

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
            ast::Expr::UnaryOp( ast::UnaryOp {
                op_kind: ast::UnaryOpKind::Not,
                argument: box ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b),
                    ..}),
                position: pos,
            }) => {
                ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(!b),
                    position: pos,
                })
            },
            ast::Expr::UnaryOp( ast::UnaryOp {
                op_kind: ast::UnaryOpKind::Not,
                argument: box ast::Expr::BinOp( ast::BinOp {
                    op_kind: ast::BinOpKind::EqCmp,
                    box left,
                    box right,
                    ..}),
                position: pos,
            }) => {
                ast::Expr::BinOp( ast::BinOp {
                    op_kind: ast::BinOpKind::NeCmp,
                    left: box left,
                    right: box right,
                    position: pos,
                })
            },
            ast::Expr::BinOp( ast::BinOp {
                op_kind: ast::BinOpKind::And,
                left: box ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b1), 
                    ..}),
                right: box ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b2),
                    ..}),
                position: pos,
            }) => {
                ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b1 && b2),
                    position: pos,
                })
            },
            ast::Expr::BinOp( ast::BinOp {
                op_kind: ast::BinOpKind::And,
                left: box ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b),
                    ..}),
                right: box conjunct,
                ..
            }) |
            ast::Expr::BinOp( ast::BinOp {
                op_kind: ast::BinOpKind::And,
                left: box conjunct,
                right: box ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b),
                    ..}),
                ..
            }) => {
                if b {
                    conjunct
                } else {
                    false.into()
                }
            },
            ast::Expr::BinOp( ast::BinOp {
                op_kind: ast::BinOpKind::Or,
                left: box ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b),
                    ..}),
                right: box disjunct,
                ..
            }) |
            ast::Expr::BinOp( ast::BinOp {
                op_kind: ast::BinOpKind::Or,
                left: box disjunct,
                right: box ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b),
                    ..}),
                ..
            }) => {
                if b {
                    true.into()
                } else {
                    disjunct
                }
            },
            ast::Expr::BinOp( ast::BinOp {
                op_kind: ast::BinOpKind::Implies,
                left: guard,
                right: box ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b),
                    ..}),
                position: pos,
            }) => {
                if b {
                    true.into()
                } else {
                    ast::Expr::UnaryOp( ast::UnaryOp {
                        op_kind: ast::UnaryOpKind::Not,
                        argument: guard,
                        position: pos,
                    })
                }
            },
            ast::Expr::BinOp( ast::BinOp {
                op_kind: ast::BinOpKind::Implies,
                left: box ast::Expr::Const( ast::ConstExpr {
                    value: ast::Const::Bool(b),
                    ..}),
                right: box body,
                ..
            }) => {
                if b {
                    body
                } else {
                    true.into()
                }
            },
            ast::Expr::BinOp( ast::BinOp {
                op_kind: ast::BinOpKind::And,
                left: box op1,
                right: box op2,
                position: pos
            }) => {
                ast::Expr::BinOp( ast::BinOp {
                    op_kind: ast::BinOpKind::And,
                    left: box self.apply_rules(op1),
                    right: box self.apply_rules(op2),
                    position: pos,
                })
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
            ast::Expr::BinOp( ast::BinOp {
                op_kind: ast::BinOpKind::And,
                left: box ast::Expr::BinOp( ast::BinOp {
                    op_kind: ast::BinOpKind::Implies,
                    left: simplified_guard.clone(),
                    right: simplified_then,
                    position: pos,
                }),
                right: box ast::Expr::BinOp( ast::BinOp {
                    op_kind: ast::BinOpKind::Implies,
                    left: box ast::Expr::UnaryOp( ast::UnaryOp {
                        op_kind: ast::UnaryOpKind::Not,
                        argument: simplified_guard,
                        position: pos,
                    }),
                    right: simplified_else,
                    position: pos,
                }),
                position: pos,
            })
        } else {
            ast::Expr::Cond( ast::Cond {
                guard: simplified_guard,
                then_expr: simplified_then,
                else_expr: simplified_else,
                position: pos,
            })
        };
        self.apply_rules(result)
    }
}
