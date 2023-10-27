use vir::{
    common::position::Positioned,
    low::{
        expression::{visitors::ExpressionFolder, BinaryOp, Constant, MagicWand, UnaryOp},
        Expression, Position,
    },
};

use crate::fol::FolStatement;

struct Optimizer {}

fn constant_at(value: bool, position: Position) -> Expression {
    vir::low::Expression::Constant(Constant {
        value: value.into(),
        ty: vir::low::Type::Bool,
        position,
    })
}

fn equal_to_const(value: &Expression, constant: bool) -> bool {
    if let vir::low::Expression::Constant(Constant {
        value: vir::low::ConstantValue::Bool(b),
        ty: vir::low::Type::Bool,
        ..
    }) = value
    {
        *b == constant
    } else {
        false
    }
}

impl ExpressionFolder for Optimizer {
    fn fold_binary_op_enum(&mut self, binary_op: BinaryOp) -> Expression {
        let new_left = self.fold_expression(*binary_op.left);
        let new_right = self.fold_expression(*binary_op.right);

        match binary_op.op_kind {
            vir::low::BinaryOpKind::EqCmp => {
                if new_left == new_right {
                    constant_at(true, binary_op.position)
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        ..binary_op
                    })
                }
            }
            vir::low::BinaryOpKind::NeCmp => {
                if new_left == new_right {
                    constant_at(false, binary_op.position)
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        ..binary_op
                    })
                }
            }
            vir::low::BinaryOpKind::And => {
                if equal_to_const(&new_left, true) {
                    new_right
                } else if equal_to_const(&new_right, true) {
                    new_left
                } else if equal_to_const(&new_left, false) {
                    constant_at(false, new_right.position())
                } else if equal_to_const(&new_right, false) {
                    constant_at(false, new_left.position())
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        ..binary_op
                    })
                }
            }
            vir::low::BinaryOpKind::Or => {
                if equal_to_const(&new_left, true) {
                    constant_at(true, new_right.position())
                } else if equal_to_const(&new_right, true) {
                    constant_at(true, new_left.position())
                } else if equal_to_const(&new_left, false) {
                    new_right
                } else if equal_to_const(&new_right, false) {
                    new_left
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        ..binary_op
                    })
                }
            }
            vir::low::BinaryOpKind::Implies => {
                if equal_to_const(&new_left, true) {
                    new_right
                } else if equal_to_const(&new_right, false) {
                    self.fold_unary_op_enum(UnaryOp {
                        op_kind: vir::low::UnaryOpKind::Not,
                        position: new_left.position(),
                        argument: Box::new(new_left),
                    })
                } else if equal_to_const(&new_left, false) {
                    constant_at(true, new_right.position())
                } else if equal_to_const(&new_right, true) {
                    constant_at(true, new_left.position())
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        ..binary_op
                    })
                }
            }
            _ => vir::low::Expression::BinaryOp(BinaryOp {
                left: Box::new(new_left),
                right: Box::new(new_right),
                ..binary_op
            }),
        }
    }

    fn fold_unary_op_enum(&mut self, unary_op: UnaryOp) -> Expression {
        let new_argument = self.fold_expression(*unary_op.argument);

        match unary_op.op_kind {
            vir::low::UnaryOpKind::Not => {
                if equal_to_const(&new_argument, true) {
                    constant_at(false, new_argument.position())
                } else if equal_to_const(&new_argument, false) {
                    constant_at(true, new_argument.position())
                } else if let vir::low::Expression::UnaryOp(UnaryOp {
                    op_kind: vir::low::UnaryOpKind::Not,
                    argument,
                    ..
                }) = new_argument
                {
                    *argument
                } else {
                    vir::low::Expression::UnaryOp(UnaryOp {
                        argument: Box::new(new_argument),
                        ..unary_op
                    })
                }
            }
            _ => vir::low::Expression::UnaryOp(UnaryOp {
                argument: Box::new(new_argument),
                ..unary_op
            }),
        }
    }

    fn fold_quantifier_enum(
        &mut self,
        quantifier: vir::low::expression::Quantifier,
    ) -> vir::low::Expression {
        if quantifier.triggers.is_empty() {
            let new_body = self.fold_expression(*quantifier.body);
            if equal_to_const(&new_body, true)
                && quantifier.kind == vir::low::expression::QuantifierKind::ForAll
            {
                constant_at(true, new_body.position())
            } else if equal_to_const(&new_body, false)
                && quantifier.kind == vir::low::expression::QuantifierKind::Exists
            {
                constant_at(false, new_body.position())
            } else {
                vir::low::Expression::Quantifier(vir::low::expression::Quantifier {
                    body: Box::new(new_body),
                    ..quantifier
                })
            }
        } else {
            quantifier.into() // cannot optimize because we might remove something that is in a trigger
        }
    }

    fn fold_magic_wand_enum(&mut self, magic_wand: vir::low::expression::MagicWand) -> Expression {
        // magic wand (--*) is basically implication, so we can simplify accordingly
        let new_left = self.fold_expression(*magic_wand.left);
        let new_right = self.fold_expression(*magic_wand.right);

        if equal_to_const(&new_left, true) {
            new_right
        } else if equal_to_const(&new_right, false) {
            self.fold_unary_op_enum(UnaryOp {
                op_kind: vir::low::UnaryOpKind::Not,
                position: new_left.position(),
                argument: Box::new(new_left),
            })
        } else if equal_to_const(&new_left, false) {
            constant_at(true, new_right.position())
        } else if equal_to_const(&new_right, true) {
            constant_at(true, new_left.position())
        } else {
            vir::low::Expression::MagicWand(MagicWand {
                left: Box::new(new_left),
                right: Box::new(new_right),
                position: magic_wand.position,
            })
        }
    }

    fn fold_conditional_enum(
        &mut self,
        conditional: vir::low::expression::Conditional,
    ) -> Expression {
        let new_cond = self.fold_expression(*conditional.guard);
        let new_true = self.fold_expression(*conditional.then_expr);
        let new_false = self.fold_expression(*conditional.else_expr);

        if equal_to_const(&new_cond, true) {
            new_true
        } else if equal_to_const(&new_cond, false) {
            new_false
        } else if new_true == new_false {
            new_true
        } else if equal_to_const(&new_true, true) && equal_to_const(&new_false, false) {
            new_cond
        } else if equal_to_const(&new_true, false) && equal_to_const(&new_false, true) {
            self.fold_unary_op_enum(UnaryOp {
                op_kind: vir::low::UnaryOpKind::Not,
                position: new_cond.position(),
                argument: Box::new(new_cond),
            })
        } else {
            vir::low::Expression::Conditional(vir::low::expression::Conditional {
                guard: Box::new(new_cond),
                then_expr: Box::new(new_true),
                else_expr: Box::new(new_false),
                position: conditional.position,
            })
        }
    }
}

pub fn optimize_statements(statements: Vec<FolStatement>) -> Vec<FolStatement> {
    statements
        .into_iter()
        .filter_map(|statement| match statement {
            FolStatement::Assume(expr) => {
                let mut optimizer = Optimizer {};
                let expr = optimizer.fold_expression(expr);
                if equal_to_const(&expr, true) {
                    None
                } else {
                    Some(FolStatement::Assume(expr))
                }
            }
            FolStatement::Assert { expression, reason } => {
                let mut optimizer = Optimizer {};
                let expression = optimizer.fold_expression(expression);
                if equal_to_const(&expression, true) {
                    None
                } else {
                    Some(FolStatement::Assert { expression, reason })
                }
            }
            x => Some(x),
        })
        .collect()
}
