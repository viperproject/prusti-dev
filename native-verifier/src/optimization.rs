use vir::low::{
    expression::{visitors::ExpressionFolder, BinaryOp, UnaryOp},
    Expression,
};

use crate::fol::FolStatement;

struct Optimizer {}

impl ExpressionFolder for Optimizer {
    fn fold_binary_op_enum(&mut self, binary_op: BinaryOp) -> Expression {
        let new_left = self.fold_expression(*binary_op.left);
        let new_right = self.fold_expression(*binary_op.right);

        match binary_op.op_kind {
            vir::low::BinaryOpKind::EqCmp => {
                if new_left == new_right {
                    true.into()
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        op_kind: vir::low::BinaryOpKind::EqCmp,
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        position: binary_op.position,
                    })
                }
            }
            vir::low::BinaryOpKind::NeCmp => {
                if new_left == new_right {
                    false.into()
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        op_kind: vir::low::BinaryOpKind::NeCmp,
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        position: binary_op.position,
                    })
                }
            }
            vir::low::BinaryOpKind::And => {
                if new_left == true.into() {
                    new_right
                } else if new_right == true.into() {
                    new_left
                } else if new_left == false.into() || new_right == false.into() {
                    false.into()
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        op_kind: vir::low::BinaryOpKind::And,
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        position: binary_op.position,
                    })
                }
            }
            vir::low::BinaryOpKind::Or => {
                if new_left == true.into() || new_right == true.into() {
                    true.into()
                } else if new_left == false.into() {
                    new_right
                } else if new_right == false.into() {
                    new_left
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        op_kind: vir::low::BinaryOpKind::Or,
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        position: binary_op.position,
                    })
                }
            }
            vir::low::BinaryOpKind::Implies => {
                if new_left == true.into() {
                    new_right
                } else if new_right == false.into() {
                    vir::low::Expression::UnaryOp(UnaryOp {
                        op_kind: vir::low::UnaryOpKind::Not,
                        argument: Box::new(new_left),
                        position: binary_op.position,
                    })
                } else if new_left == false.into() {
                    true.into()
                } else if new_right == true.into() {
                    true.into()
                } else {
                    vir::low::Expression::BinaryOp(BinaryOp {
                        op_kind: vir::low::BinaryOpKind::Implies,
                        left: Box::new(new_left),
                        right: Box::new(new_right),
                        position: binary_op.position,
                    })
                }
            }
            typ => vir::low::Expression::BinaryOp(BinaryOp {
                op_kind: typ,
                left: Box::new(new_left),
                right: Box::new(new_right),
                position: binary_op.position,
            }),
        }
    }

    fn fold_unary_op_enum(&mut self, unary_op: UnaryOp) -> Expression {
        let new_argument = self.fold_expression(*unary_op.argument);

        match unary_op.op_kind {
            vir::low::UnaryOpKind::Not => {
                if new_argument == true.into() {
                    false.into()
                } else if new_argument == false.into() {
                    true.into()
                } else if let vir::low::Expression::UnaryOp(UnaryOp {
                    op_kind: vir::low::UnaryOpKind::Not,
                    argument,
                    ..
                }) = new_argument
                {
                    *argument
                } else {
                    vir::low::Expression::UnaryOp(UnaryOp {
                        op_kind: vir::low::UnaryOpKind::Not,
                        argument: Box::new(new_argument),
                        position: unary_op.position,
                    })
                }
            }
            typ => vir::low::Expression::UnaryOp(UnaryOp {
                op_kind: typ,
                argument: Box::new(new_argument),
                position: unary_op.position,
            }),
        }
    }

    fn fold_conditional_enum(
        &mut self,
        conditional: vir::low::expression::Conditional,
    ) -> Expression {
        let new_cond = self.fold_expression(*conditional.guard);
        let new_true = self.fold_expression(*conditional.then_expr);
        let new_false = self.fold_expression(*conditional.else_expr);

        if new_cond == true.into() {
            new_true
        } else if new_cond == false.into() {
            new_false
        } else if new_true == new_false {
            new_true
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
                if expr == true.into() {
                    None
                } else {
                    Some(FolStatement::Assume(expr))
                }
            }
            FolStatement::Assert(expr) => {
                let mut optimizer = Optimizer {};
                let expr = optimizer.fold_expression(expr);
                if expr == true.into() {
                    None
                } else {
                    Some(FolStatement::Assert(expr))
                }
            }
            x => Some(x),
        })
        .collect()
}
