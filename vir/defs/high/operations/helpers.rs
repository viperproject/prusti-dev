use super::super::ast::expression::*;
use crate::common::expression::*;

impl BinaryOperationHelpers for Expression {
    type BinaryOperationKind = BinOpKind;
    fn binary_operation(kind: Self::BinaryOperationKind, left: Self, right: Self) -> Self {
        Self::BinOp(BinOp {
            op_kind: kind,
            left: Box::new(left),
            right: Box::new(right),
            position: Default::default(),
        })
    }
    fn equals(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::EqCmp, left, right)
    }
    fn not_equals(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::NeCmp, left, right)
    }
    fn greater_than(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::GtCmp, left, right)
    }
    fn greater_equals(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::GeCmp, left, right)
    }
    fn less_than(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::LtCmp, left, right)
    }
    fn less_equals(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::LeCmp, left, right)
    }
    fn add(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::Add, left, right)
    }
    fn subtract(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::Sub, left, right)
    }
    fn multiply(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::Mul, left, right)
    }
    fn divide(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::Div, left, right)
    }
    fn module(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::Mod, left, right)
    }
    fn and(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::And, left, right)
    }
    fn or(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::Or, left, right)
    }
    fn implies(left: Self, right: Self) -> Self {
        Self::binary_operation(BinOpKind::Implies, left, right)
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
