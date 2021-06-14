vir_raw_block! { Variable =>
    impl std::fmt::Display for Variable {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.name.fmt(f)
        }
    }
}
vir_raw_block! { Constant =>
    impl std::fmt::Display for Constant {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Constant::Bool(value) => value.fmt(f),
                Constant::Int(value) => value.fmt(f),
            }
        }
    }
}
vir_raw_block! { UnaryOperation =>
    impl std::fmt::Display for UnaryOperation {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self.kind {
                UnaryOperationKind::Not => write!(f, "!")?,
                UnaryOperationKind::Minus => write!(f, "-")?,
            }
            write!(f, "{}", self.arg)
        }
    }
}
vir_raw_block! { BinaryOperation =>
    impl std::fmt::Display for BinaryOperation {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "({}{}{})", self.left, self.kind, self.right)
        }
    }
}
vir_raw_block! { BinaryOperationKind =>
    impl std::fmt::Display for BinaryOperationKind {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                BinaryOperationKind::EqCmp => write!(f, "=="),
                BinaryOperationKind::NeCmp => write!(f, "!="),
                BinaryOperationKind::GtCmp => write!(f, ">"),
                BinaryOperationKind::GeCmp => write!(f, ">="),
                BinaryOperationKind::LtCmp => write!(f, "<"),
                BinaryOperationKind::LeCmp => write!(f, "<="),
                BinaryOperationKind::Add => write!(f, "+"),
                BinaryOperationKind::Sub => write!(f, "-"),
                BinaryOperationKind::Mul => write!(f, "*"),
                BinaryOperationKind::Div => write!(f, "/"),
                BinaryOperationKind::Mod => write!(f, "%"),
                BinaryOperationKind::And => write!(f, "&&"),
                BinaryOperationKind::Or => write!(f, "||"),
                BinaryOperationKind::Implies => write!(f, "==>"),
            }
        }
    }
}
vir_raw_block! { Conditional =>
    impl std::fmt::Display for Conditional {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(
                f,
                "{} ? {} : {}",
                self.guard, self.then_expr, self.else_expr
            )
        }
    }
}
vir_raw_block! { Quantifier =>
    impl std::fmt::Display for Quantifier {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}(|", self.kind)?;
            for variable in &self.variables {
                write!(f, "{}, ", variable)?;
            }
            write!(f, "| {} [", self.body)?;
            for trigger in &self.triggers {
                write!(f, "({}),", trigger)?;
            }
            write!(f, "])")
        }
    }
}
vir_raw_block! { QuantifierKind =>
    impl std::fmt::Display for QuantifierKind {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                QuantifierKind::ForAll => write!(f, "forall"),
                QuantifierKind::Exists => write!(f, "exists"),
            }
        }
    }
}
vir_raw_block! { BoundedVariableDecl =>
    impl std::fmt::Display for BoundedVariableDecl {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}: {}", self.name, self.sort)
        }
    }
}
vir_raw_block! { Trigger =>
    impl std::fmt::Display for Trigger {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            for part in &self.parts {
                write!(f, "{},", part)?;
            }
            Ok(())
        }
    }
}
vir_raw_block! { FunctionApplication =>
    impl std::fmt::Display for FunctionApplication {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}(", self.function)?;
            for arg in &self.args {
                write!(f, "{}, ", arg)?;
            }
            write!(f, ")")
        }
    }
}
vir_raw_block! { LabelledExpression =>
    impl std::fmt::Display for LabelledExpression {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self.positivity {
                LabelPositivity::Positive => write!(f, "lblpos")?,
                LabelPositivity::Negative => write!(f, "lblneg")?,
            }
            write!(f, "({}: {})", self.name, self.expression)
        }
    }
}
