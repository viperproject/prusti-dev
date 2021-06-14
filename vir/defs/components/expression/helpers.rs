use super::*;

vir_raw_block! { VariableHelpers =>
    impl crate::common::expression::VariableHelpers for Expression {
        type VariableSymbol = VariableSymbol;
        fn variable(name: VariableSymbol) -> Expression {
            Expression::Variable(Variable { name })
        }
    }
    impl From<Variable> for Expression {
        fn from(variable: Variable) -> Self {
            Self::Variable(variable)
        }
    }
}

vir_raw_block! { ConstantHelpers =>
    impl crate::common::expression::ConstantHelpers for Expression {
        type Constant = Constant;
        fn constant(constant: Constant) -> Expression {
            Expression::Constant(constant)
        }
        fn bool(value: bool) -> Expression {
            Expression::constant(Constant::Bool(value))
        }
        fn int(value: i64) -> Expression {
            Expression::constant(Constant::Int(value))
        }
    }
    impl From<bool> for Constant {
        fn from(value: bool) -> Self {
            Constant::Bool(value)
        }
    }
    impl From<i64> for Constant {
        fn from(value: i64) -> Self {
            Constant::Int(value)
        }
    }
    impl From<bool> for Expression {
        fn from(value: bool) -> Self {
            Self::bool(value)
        }
    }
    impl From<i64> for Expression {
        fn from(value: i64) -> Self {
            Self::int(value)
        }
    }
    impl From<Constant> for Expression {
        fn from(constant: Constant) -> Self {
            Self::Constant(constant)
        }
    }
}

vir_raw_block! { UnaryOperationHelpers =>
    impl crate::common::expression::UnaryOperationHelpers for Expression {
        type UnaryOperationKind = UnaryOperationKind;
        fn unary_operation(kind: UnaryOperationKind, arg: Expression) -> Expression {
            Expression::UnaryOperation(UnaryOperation {
                kind,
                arg: Box::new(arg),
            })
        }
        fn not(arg: Expression) -> Expression {
            Expression::unary_operation(UnaryOperationKind::Not, arg)
        }
        fn minus(arg: Expression) -> Expression {
            Expression::unary_operation(UnaryOperationKind::Minus, arg)
        }
    }
    impl From<UnaryOperation> for Expression {
        fn from(operation: UnaryOperation) -> Self {
            Self::UnaryOperation(operation)
        }
    }
}

vir_raw_block! { BinaryOperationHelpers =>
    impl crate::common::expression::BinaryOperationHelpers for Expression {
        type BinaryOperationKind = BinaryOperationKind;
        fn binary_operation(kind: BinaryOperationKind, left: Expression, right: Expression) -> Expression {
            Expression::BinaryOperation(BinaryOperation {
                kind,
                left: Box::new(left),
                right: Box::new(right),
            })
        }
        fn equals(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::EqCmp, left, right)
        }
        fn not_equals(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::NeCmp, left, right)
        }
        fn greater_than(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::GtCmp, left, right)
        }
        fn greater_equals(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::GeCmp, left, right)
        }
        fn less_than(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::LtCmp, left, right)
        }
        fn less_equals(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::LeCmp, left, right)
        }
        fn add(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::Add, left, right)
        }
        fn subtract(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::Sub, left, right)
        }
        fn multiply(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::Mul, left, right)
        }
        fn divide(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::Div, left, right)
        }
        fn module(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::Mod, left, right)
        }
        fn and(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::And, left, right)
        }
        fn or(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::Or, left, right)
        }
        fn implies(left: Expression, right: Expression) -> Expression {
            Self::binary_operation(BinaryOperationKind::Implies, left, right)
        }
    }
    impl From<BinaryOperation> for Expression {
        fn from(operation: BinaryOperation) -> Self {
            Self::BinaryOperation(operation)
        }
    }
}

vir_raw_block! { QuantifierHelpers =>
    impl crate::common::expression::QuantifierHelpers for Expression {
        type QuantifierKind = QuantifierKind;
        type BoundedVariableDecl = BoundedVariableDecl;
        type Trigger = Trigger;
        fn quantifier(
            kind: QuantifierKind,
            variables: Vec<BoundedVariableDecl>,
            triggers: Vec<Trigger>,
            body: Expression,
        ) -> Expression {
            Expression::Quantifier(Quantifier {
                kind,
                variables,
                triggers,
                body: Box::new(body),
            })
        }
        fn forall(
            variables: Vec<BoundedVariableDecl>,
            triggers: Vec<Trigger>,
            body: Expression,
        ) -> Expression {
            Self::quantifier(QuantifierKind::ForAll, variables, triggers, body)
        }
        fn exists(
            variables: Vec<BoundedVariableDecl>,
            triggers: Vec<Trigger>,
            body: Expression,
        ) -> Expression {
            Self::quantifier(QuantifierKind::Exists, variables, triggers, body)
        }
    }
    impl From<Quantifier> for Expression {
        fn from(quantifier: Quantifier) -> Self {
            Self::Quantifier(quantifier)
        }
    }
}

vir_raw_block! { FunctionApplicationHelpers =>
    impl crate::common::expression::FunctionApplicationHelpers for Expression {
        type FunctionSymbol = FunctionSymbol;
        fn call(function: FunctionSymbol, args: Vec<Expression>) -> Expression {
            Self::FunctionApplication(FunctionApplication {
                function,
                args,
            })
        }
    }
    impl From<FunctionApplication> for Expression {
        fn from(application: FunctionApplication) -> Self {
            Self::FunctionApplication(application)
        }
    }
}

vir_raw_block! { LabelledExpressionHelpers =>
    impl crate::common::expression::LabelledExpressionHelpers for Expression {
        type LabelPositivity = LabelPositivity;
        type LabelSymbol = LabelSymbol;
        fn labelled_expression(
            positivity: LabelPositivity,
            name: LabelSymbol,
            expression: Expression
        ) -> Expression {
            Expression::LabelledExpression(LabelledExpression {
                positivity,
                name,
                expression: Box::new(expression),
            })
        }
        fn label_negative(name: LabelSymbol, expression: Expression) -> Expression {
            Self::labelled_expression(LabelPositivity::Negative, name, expression)
        }
        fn label_positive(name: LabelSymbol, expression: Expression) -> Expression {
            Self::labelled_expression(LabelPositivity::Positive, name, expression)
        }
    }
    impl From<LabelledExpression> for Expression {
        fn from(expression: LabelledExpression) -> Self {
            Self::LabelledExpression(expression)
        }
    }
}
