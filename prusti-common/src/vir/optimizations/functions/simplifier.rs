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
    #[tracing::instrument(level = "debug", skip(self), fields(self = %self), ret(Display))]
    fn simplify(mut self) -> Self {
        trace!("[enter] simplify = {}", self);
        let new_body = self.body.map(|b| b.simplify());
        self.body = new_body;
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
    #[tracing::instrument(level = "debug", skip(e), fields(e = %e), ret(Display))]
    fn apply_rules(e: ast::Expr) -> ast::Expr {
        match e {
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
            }) if !matches!(left.get_type(), ast::Type::Float(_)) => ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::NeCmp,
                left: Box::new(left),
                right: Box::new(right),
                position: pos,
            })
            .set_default_pos(inner_pos),
            ast::Expr::UnaryOp(ast::UnaryOp {
                op_kind: ast::UnaryOpKind::Not,
                argument:
                    box ast::Expr::BinOp(ast::BinOp {
                        op_kind: ast::BinaryOpKind::NeCmp,
                        box left,
                        box right,
                        position: inner_pos,
                    }),
                position: pos,
            }) if !matches!(left.get_type(), ast::Type::Float(_)) => ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::EqCmp,
                left: Box::new(left),
                right: Box::new(right),
                position: pos,
            })
            .set_default_pos(inner_pos),
            ast::Expr::UnaryOp(ast::UnaryOp {
                op_kind: ast::UnaryOpKind::Not,
                argument:
                    box ast::Expr::UnaryOp(ast::UnaryOp {
                        op_kind: ast::UnaryOpKind::Not,
                        box argument,
                        position: inner_pos,
                    }),
                position: pos,
            }) => argument,
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
            }) => {
                if b {
                    conjunct
                } else {
                    Into::<ast::Expr>::into(false).set_pos(inner_pos)
                }
            }
            .set_default_pos(pos),
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
            }) => {
                if b {
                    Into::<ast::Expr>::into(true).set_pos(inner_pos)
                } else {
                    disjunct
                }
            }
            .set_default_pos(pos),
            ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::Implies,
                left: guard,
                right:
                    box ast::Expr::Const(ast::ConstExpr {
                        value: ast::Const::Bool(b),
                        position: inner_pos,
                    }),
                position: pos,
            }) => {
                if b {
                    Into::<ast::Expr>::into(true).set_pos(pos)
                } else {
                    ast::Expr::UnaryOp(ast::UnaryOp {
                        op_kind: ast::UnaryOpKind::Not,
                        argument: guard,
                        position: pos,
                    })
                }
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
            }) => {
                if b {
                    body
                } else {
                    Into::<ast::Expr>::into(true).set_pos(inner_pos)
                }
            }
            .set_default_pos(pos),
            ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::And,
                left: box op1,
                right: box op2,
                position: pos,
            }) => ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::And,
                left: Box::new(Self::apply_rules(op1)),
                right: Box::new(Self::apply_rules(op2)),
                position: pos,
            }),
            // added to satisfy Viper because we don't do desugaring of quantified permissions
            // elsewhere; consider calling the Viper functions that does that instead
            ast::Expr::ForAll(ast::ForAll {
                variables: vars,
                triggers: trigs,
                body:
                    box ast::Expr::BinOp(ast::BinOp {
                        op_kind: ast::BinaryOpKind::Implies,
                        left: box c0,
                        right:
                            box ast::Expr::BinOp(ast::BinOp {
                                op_kind: ast::BinaryOpKind::Implies,
                                left: box c1,
                                right: box ex,
                                ..
                            }),
                        position: pos0,
                    }),
                position: pos_quant,
            }) if !ex.is_pure() => Self::apply_rules(ast::Expr::ForAll(ast::ForAll {
                variables: vars,
                triggers: trigs,
                body: Box::new(ast::Expr::BinOp(ast::BinOp {
                    op_kind: ast::BinaryOpKind::Implies,
                    left: Box::new(ast::Expr::BinOp(ast::BinOp {
                        op_kind: ast::BinaryOpKind::And,
                        left: Box::new(c0),
                        right: Box::new(c1),
                        position: pos0,
                    })),
                    right: Box::new(ex),
                    position: pos0,
                })),
                position: pos_quant,
            })),
            // same comment as above
            ast::Expr::ForAll(ast::ForAll {
                variables: vars,
                triggers: trigs,
                body:
                    box ast::Expr::BinOp(ast::BinOp {
                        op_kind: ast::BinaryOpKind::Implies,
                        left: box cond,
                        right:
                            box ast::Expr::BinOp(ast::BinOp {
                                op_kind: ast::BinaryOpKind::And,
                                left: box part0,
                                right: box part1,
                                ..
                            }),
                        position: pos_body,
                    }),
                position: pos_quant,
            }) if !part0.is_pure() || !part1.is_pure() => ast::Expr::BinOp(ast::BinOp {
                op_kind: ast::BinaryOpKind::And,
                left: Box::new(Self::apply_rules(ast::Expr::ForAll(ast::ForAll {
                    variables: vars.clone(),
                    triggers: trigs.clone(),
                    body: Box::new(ast::Expr::BinOp(ast::BinOp {
                        op_kind: ast::BinaryOpKind::Implies,
                        left: Box::new(cond.clone()),
                        right: Box::new(part0),
                        position: pos_body,
                    })),
                    position: pos_quant,
                }))),
                right: Box::new(Self::apply_rules(ast::Expr::ForAll(ast::ForAll {
                    variables: vars,
                    triggers: trigs,
                    body: Box::new(ast::Expr::BinOp(ast::BinOp {
                        op_kind: ast::BinaryOpKind::Implies,
                        left: Box::new(cond),
                        right: Box::new(part1),
                        position: pos_body,
                    })),
                    position: pos_quant,
                }))),
                position: pos_quant,
            }),
            r => r,
        }
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
                left: Box::new(ast::Expr::BinOp(ast::BinOp {
                    op_kind: ast::BinaryOpKind::Implies,
                    left: simplified_guard.clone(),
                    right: simplified_then,
                    position,
                })),
                right: Box::new(ast::Expr::BinOp(ast::BinOp {
                    op_kind: ast::BinaryOpKind::Implies,
                    left: Box::new(ast::Expr::UnaryOp(ast::UnaryOp {
                        op_kind: ast::UnaryOpKind::Not,
                        argument: simplified_guard,
                        position,
                    })),
                    right: simplified_else,
                    position,
                })),
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
