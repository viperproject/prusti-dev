use super::*;

vir_raw_block! { Variable =>
    impl crate::common::expression::SyntacticEvaluation for Variable {
        fn is_true(&self) -> bool {
            false
        }
        fn is_false(&self) -> bool {
            false
        }
    }
}
vir_raw_block! { Constant =>
    impl crate::common::expression::SyntacticEvaluation for Constant {
        fn is_true(&self) -> bool {
            match self {
                Constant::Bool(value) => *value,
                Constant::Int(_) => false,
            }
        }
        fn is_false(&self) -> bool {
            match self {
                Constant::Bool(value) => !*value,
                Constant::Int(_) => false,
            }
        }
    }
}
vir_raw_block! { UnaryOperation =>
    impl crate::common::expression::SyntacticEvaluation for UnaryOperation {
        fn is_true(&self) -> bool {
            match self.kind {
                UnaryOperationKind::Not => self.arg.is_false(),
                UnaryOperationKind::Minus => unreachable!(),
            }
        }
        fn is_false(&self) -> bool {
            match self.kind {
                UnaryOperationKind::Not => self.arg.is_true(),
                UnaryOperationKind::Minus => unreachable!(),
            }
        }
    }
}
vir_raw_block! { BinaryOperation =>
    impl crate::common::expression::SyntacticEvaluation for BinaryOperation {
        fn is_true(&self) -> bool {
            match self.kind {
                BinaryOperationKind::EqCmp => self.left == self.right,
                | BinaryOperationKind::NeCmp
                | BinaryOperationKind::GtCmp
                | BinaryOperationKind::GeCmp
                | BinaryOperationKind::LtCmp
                | BinaryOperationKind::LeCmp => false,
                BinaryOperationKind::And => {
                    self.left.is_true() && self.right.is_true()
                }
                BinaryOperationKind::Or => {
                    self.left.is_true() || self.right.is_true()
                }
                BinaryOperationKind::Implies => {
                    self.left.is_false() || self.right.is_true()
                }
                BinaryOperationKind::Add
                | BinaryOperationKind::Sub
                | BinaryOperationKind::Mul
                | BinaryOperationKind::Div
                | BinaryOperationKind::Mod => unreachable!(),
            }
        }
        fn is_false(&self) -> bool {
            match self.kind {
                | BinaryOperationKind::EqCmp
                | BinaryOperationKind::NeCmp
                | BinaryOperationKind::GtCmp
                | BinaryOperationKind::GeCmp
                | BinaryOperationKind::LtCmp
                | BinaryOperationKind::LeCmp => false,
                BinaryOperationKind::And => {
                    self.left.is_false() || self.right.is_false()
                }
                BinaryOperationKind::Or => {
                    self.left.is_false() && self.right.is_false()
                }
                BinaryOperationKind::Implies => {
                    self.left.is_true() && self.right.is_false()
                }
                BinaryOperationKind::Add
                | BinaryOperationKind::Sub
                | BinaryOperationKind::Mul
                | BinaryOperationKind::Div
                | BinaryOperationKind::Mod => unreachable!(),
            }
        }
    }
}
vir_raw_block! { Conditional =>
    impl crate::common::expression::SyntacticEvaluation for Conditional {
        fn is_true(&self) -> bool {
            self.then_expr.is_true() && self.else_expr.is_true()
        }
        fn is_false(&self) -> bool {
            self.then_expr.is_false() && self.else_expr.is_false()
        }
    }
}
vir_raw_block! { Quantifier =>
    impl crate::common::expression::SyntacticEvaluation for Quantifier {
        fn is_true(&self) -> bool {
            false
        }
        fn is_false(&self) -> bool {
            false
        }
    }
}
vir_raw_block! { FunctionApplication =>
    impl crate::common::expression::SyntacticEvaluation for FunctionApplication {
        fn is_true(&self) -> bool {
            false
        }
        fn is_false(&self) -> bool {
            false
        }
    }
}
vir_raw_block! { LabelledExpression =>
    impl crate::common::expression::SyntacticEvaluation for LabelledExpression {
        fn is_true(&self) -> bool {
            self.expression.is_true()
        }
        fn is_false(&self) -> bool {
            self.expression.is_false()
        }
    }
}
