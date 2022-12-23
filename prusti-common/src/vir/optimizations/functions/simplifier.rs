// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Function simplifier that simplifies expressions.

use crate::vir::polymorphic_vir::ast::{self, ExprFolder};
use log::trace;

pub trait Simplifier {
    /// Simplify by doing constant evaluation.
    #[must_use]
    fn simplify(self) -> Self;
}

impl Simplifier for ast::Function {
    /// Simplify functions in a way that tries to work-around regressions caused by
    /// <https://github.com/viperproject/silicon/issues/387>
    fn simplify(mut self) -> Self {
        trace!("[enter] simplify = {}", self);
        self.body = self.body.map(|b| b.simplify());
        self.posts = self.posts.into_iter().map(|p| p.simplify()).collect();
        self.pres = self.pres.into_iter().map(|p| p.simplify()).collect();
        trace!("[exit] simplify = {}", self);
        self
    }
}

impl Simplifier for ast::Expr {
    #[must_use]
    fn simplify(self) -> Self {
        trace!("[enter] simplify = {:?}", self);
        let mut folder = ExprSimplifier {};
        let res = folder.fold(self);
        trace!("[exit] simplify = {:?}", res);
        res
    }
}

struct ExprSimplifier {}

impl ExprSimplifier {
    fn apply_rules(e: ast::Expr) -> ast::Expr {
        trace!("[enter] apply_rules={}", e);
        let result = match e {
            ast::Expr::UnaryOp(ast::UnaryOp {
                op_kind: ast::UnaryOpKind::Not,
                argument:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b),
                        position: inner_pos,
                    }),
                position: pos,
            }) => ast::Expr::Const(ast::ConstExpr {
                value: ast::Const::Bool(!b),
                position: pos,
            })
            .set_default_pos(inner_pos),
            ast::Expr::UnaryOp(ast::UnaryOp {
                op_kind: ast::UnaryOpKind::Not,
                argument:
                    box ast::Expr::BinOp(ast::BinOp {
                        op_kind: ast::BinaryOpKind::EqCmp,
                        box left,
                        box right,
                        position: inner_pos,
                    }),
                position: pos,
            }) => ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::NeCmp,
                left: box left,
                right: box right,
                position: pos,
            })
            .set_default_pos(inner_pos),
            ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::And,
                left:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b1),
                        position: inner_pos1,
                    }),
                right:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b2),
                        position: inner_pos2,
                    }),
                position: pos,
            }) => ast::Expr::Const(ast::ConstExpr {
                value: ast::Const::Bool(b1 && b2),
                position: pos,
            })
            .set_default_pos(inner_pos1)
            .set_default_pos(inner_pos2),
            ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::And,
                left:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b),
                        position: inner_pos,
                    }),
                right: box conjunct,
                position: pos,
            })
            | ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::And,
                left: box conjunct,
                right:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b),
                        position: inner_pos,
                    }),
                position: pos,
            }) => if b { conjunct } else { false.into() }
                .set_pos(pos)
                .set_default_pos(inner_pos),
            ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::Or,
                left:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b),
                        position: inner_pos,
                    }),
                right: box disjunct,
                position: pos,
            })
            | ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::Or,
                left: box disjunct,
                right:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b),
                        position: inner_pos,
                    }),
                position: pos,
            }) => if b { true.into() } else { disjunct }
                .set_pos(pos)
                .set_default_pos(inner_pos),
            ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::Implies,
                left: guard,
                right:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b),
                        position: inner_pos,
                    }),
                position: pos,
            }) => if b {
                Into::<ast::Expr>::into(true).set_pos(pos)
            } else {
                ast::Expr::UnaryOp(ast::UnaryOp {
                    op_kind: ast::UnaryOpKind::Not,
                    argument: guard,
                    position: pos,
                })
            }
            .set_default_pos(inner_pos),
            ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::Implies,
                left:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b),
                        position: inner_pos,
                    }),
                right: box body,
                position: pos,
            }) => if b { body } else { true.into() }
                .set_pos(pos)
                .set_default_pos(inner_pos),
            ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::And,
                left: box op1,
                right: box op2,
                position: pos,
            }) => ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::And,
                left: box Self::apply_rules(op1),
                right: box Self::apply_rules(op2),
                position: pos,
            }),
            r => r,
        };
        trace!("[exit] apply_rules={}", result);
        result
    }
}

impl ExprFolder for ExprSimplifier {
    fn fold(&mut self, e: ast::Expr) -> ast::Expr {
        let folded_expr = ast::default_fold_expr(self, e);
        Self::apply_rules(folded_expr)
    }
    fn fold_cond(
        &mut self,
        ast::Cond {
            guard,
            then_expr,
            else_expr,
            position,
        }: ast::Cond,
    ) -> ast::Expr {
        let simplified_guard = self.fold_boxed(guard);
        let simplified_then = self.fold_boxed(then_expr);
        let simplified_else = self.fold_boxed(else_expr);
        let result = if simplified_then.is_bool() || simplified_else.is_bool() {
            ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::And,
                left: box ast::Expr::BinOp(ast::BinOp {
                    op_kind: ast::BinaryOpKind::Implies,
                    left: simplified_guard.clone(),
                    right: simplified_then,
                    position,
                }),
                right: box ast::Expr::BinOp(ast::BinOp {
                    op_kind: ast::BinaryOpKind::Implies,
                    left: box ast::Expr::UnaryOp(ast::UnaryOp {
                        op_kind: ast::UnaryOpKind::Not,
                        argument: simplified_guard,
                        position,
                    }),
                    right: simplified_else,
                    position,
                }),
                position,
            })
        } else {
            ast::Expr::Cond(ast::Cond {
                guard: simplified_guard,
                then_expr: simplified_then,
                else_expr: simplified_else,
                position,
            })
        };
        Self::apply_rules(result)
    }
}
