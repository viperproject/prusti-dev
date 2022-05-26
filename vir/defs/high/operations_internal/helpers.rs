use super::super::ast::expression::*;
use crate::common::expression::*;

impl UnaryOperationHelpers for Expression {
    type UnaryOperationKind = UnaryOpKind;
    fn unary_operation(kind: Self::UnaryOperationKind, arg: Self) -> Self {
        Self::UnaryOp(UnaryOp {
            op_kind: kind,
            argument: Box::new(arg),
            position: Default::default(),
        })
    }
    fn not(arg: Self) -> Self {
        Self::unary_operation(UnaryOpKind::Not, arg)
    }
    fn minus(arg: Self) -> Self {
        Self::unary_operation(UnaryOpKind::Minus, arg)
    }
}

impl BinaryOperationHelpers for Expression {
    type BinaryOperationKind = BinaryOpKind;
    fn binary_operation(kind: Self::BinaryOperationKind, left: Self, right: Self) -> Self {
        Self::BinaryOp(BinaryOp {
            op_kind: kind,
            left: Box::new(left),
            right: Box::new(right),
            position: Default::default(),
        })
    }
    fn equals(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::EqCmp, left, right)
    }
    fn not_equals(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::NeCmp, left, right)
    }
    fn greater_than(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::GtCmp, left, right)
    }
    fn greater_equals(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::GeCmp, left, right)
    }
    fn less_than(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::LtCmp, left, right)
    }
    fn less_equals(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::LeCmp, left, right)
    }
    fn add(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::Add, left, right)
    }
    fn subtract(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::Sub, left, right)
    }
    fn multiply(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::Mul, left, right)
    }
    fn divide(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::Div, left, right)
    }
    fn module(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::Mod, left, right)
    }
    fn and(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::And, left, right)
    }
    fn or(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::Or, left, right)
    }
    fn implies(left: Self, right: Self) -> Self {
        Self::binary_operation(BinaryOpKind::Implies, left, right)
    }
}

impl QuantifierHelpers for Expression {
    type QuantifierKind = QuantifierKind;
    type BoundedVariableDecl = VariableDecl;
    type Trigger = Trigger;
    fn quantifier(
        kind: Self::QuantifierKind,
        variables: Vec<Self::BoundedVariableDecl>,
        triggers: Vec<Self::Trigger>,
        body: Self,
    ) -> Self {
        Self::quantifier_no_pos(kind, variables, triggers, body)
    }
    fn forall(
        variables: Vec<Self::BoundedVariableDecl>,
        triggers: Vec<Self::Trigger>,
        body: Self,
    ) -> Self {
        Self::quantifier_no_pos(QuantifierKind::ForAll, variables, triggers, body)
    }
    fn exists(
        variables: Vec<Self::BoundedVariableDecl>,
        triggers: Vec<Self::Trigger>,
        body: Self,
    ) -> Self {
        Self::quantifier_no_pos(QuantifierKind::Exists, variables, triggers, body)
    }
}

impl ConstantHelpers for Expression {
    fn bool(value: bool) -> Self {
        value.into()
    }
    fn int(value: i64) -> Self {
        value.into()
    }
}
