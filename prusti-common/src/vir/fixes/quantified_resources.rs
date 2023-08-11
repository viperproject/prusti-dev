// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Desugar quantified permissions syntax.

use crate::vir::polymorphic_vir::{
    ast,
    ast::{ExprFolder, StmtFolder},
    Program,
};

/// During the translation step from the parse AST to real Viper AST,
/// Silver desugars the quantified permissions syntax so that all
/// quantified permissions quantifiers have the form forall xs ::
/// c(xs) ==> acc(...) for some condition c and access acc(...).
/// Backend verifiers rely on this and crash otherwise. Since we
/// directly generate Viper AST and in Silver, this desugaring step
/// is built into the Translator (so we can't call it in Silver as a
/// separate pass), we do the desugaring ourselves here.

pub fn desugar_quantified_resources(program: Program) -> Program {
    // add other parts of the Viper program to desugar if needed
    let Program {
        functions, methods, ..
    } = program;

    let desugared_functions = functions
        .into_iter()
        .map(|f| {
            let ast::Function { body, .. } = f;
            ast::Function {
                body: body.map(|expr| ExprFolder::fold(&mut Desugarer {}, expr)),
                ..f
            }
        })
        .collect::<Vec<_>>();

    let desugared_methods = methods
        .into_iter()
        .map(|m| m.patch_statements(|stmt| Ok(StmtFolder::fold(&mut Desugarer {}, stmt))))
        .collect::<Result<Vec<_>, ()>>()
        .unwrap();

    Program {
        functions: desugared_functions,
        methods: desugared_methods,
        ..program
    }
}

struct Desugarer;

impl Desugarer {
    fn desugar(e: ast::Expr) -> ast::Expr {
        match e {
            // transform (forall A) into (forall true ==> A) if A is not an implication
            ast::Expr::ForAll(ast::ForAll {
                variables,
                triggers,
                body: box body,
                position,
            }) if !body.is_pure()
                && !matches!(
                    body,
                    ast::Expr::BinOp(ast::BinOp {
                        op_kind: ast::BinaryOpKind::Implies,
                        ..
                    })
                ) =>
            {
                Self::desugar(
                    ast::Expr::forall(
                        variables,
                        triggers,
                        ast::Expr::implies(true.into(), body.clone()).set_pos(body.pos()),
                    )
                    .set_pos(position),
                )
            }
            // transform (forall A ==> B ==> C) into (forall (A && B) ==> C)
            ast::Expr::ForAll(ast::ForAll {
                variables,
                triggers,
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
                        position: pos_body,
                    }),
                position: pos_quant,
            }) if !ex.is_pure() => Self::desugar(
                ast::Expr::forall(
                    variables,
                    triggers,
                    ast::Expr::implies(ast::Expr::and(c0, c1).set_pos(pos_body), ex)
                        .set_pos(pos_body),
                )
                .set_pos(pos_quant),
            ),
            // transform (forall A ==> (B ? C : D)) into (forall A ==> ((B ==> C) && (!B ==> D)))
            ast::Expr::ForAll(ast::ForAll {
                variables,
                triggers,
                body:
                    box ast::Expr::BinOp(ast::BinOp {
                        op_kind: ast::BinaryOpKind::Implies,
                        left: box filter,
                        right:
                            box ast::Expr::Cond(ast::Cond {
                                guard: box guard,
                                then_expr: box then_expr,
                                else_expr: box else_expr,
                                position: pos_cond,
                            }),
                        position: pos_body,
                    }),
                position: pos_quant,
            }) if !then_expr.is_pure() || !else_expr.is_pure() => Self::desugar(
                ast::Expr::forall(
                    variables,
                    triggers,
                    ast::Expr::implies(
                        filter,
                        ast::Expr::and(
                            ast::Expr::implies(guard.clone(), then_expr).set_pos(pos_cond),
                            ast::Expr::implies(ast::Expr::not(guard).set_pos(pos_cond), else_expr),
                        )
                        .set_pos(pos_cond),
                    )
                    .set_pos(pos_body),
                )
                .set_pos(pos_quant),
            ),
            // transform (forall A ==> (B && C)) into ((forall A ==> B) && (forall A ==> C))
            ast::Expr::ForAll(ast::ForAll {
                variables,
                triggers,
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
            }) if !part0.is_pure() || !part1.is_pure() => ast::Expr::and(
                Self::desugar(
                    ast::Expr::forall(
                        variables.clone(),
                        triggers.clone(),
                        ast::Expr::implies(cond.clone(), part0).set_pos(pos_body),
                    )
                    .set_pos(pos_quant),
                ),
                Self::desugar(
                    ast::Expr::forall(
                        variables,
                        triggers,
                        ast::Expr::implies(cond, part1).set_pos(pos_body),
                    )
                    .set_pos(pos_quant),
                ),
            )
            .set_pos(pos_quant),
            r => r,
        }
    }
}

impl ExprFolder for Desugarer {
    fn fold(&mut self, e: ast::Expr) -> ast::Expr {
        let folded_expr = ast::default_fold_expr(self, e);
        Self::desugar(folded_expr)
    }
}

impl StmtFolder for Desugarer {
    fn fold_expr(&mut self, e: ast::Expr) -> ast::Expr {
        ExprFolder::fold(self, e)
    }
}
