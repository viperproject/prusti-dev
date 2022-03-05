pub(crate) use super::super::{
    expression::{BinaryOpKind, Expression, UnaryOpKind},
    ty::Type,
    Position,
};
use crate::common::display;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant)]
#[allow(clippy::large_enum_variant)]
pub enum Rvalue {
    UnaryOp(UnaryOp),
    BinaryOp(BinaryOp),
    Discriminant(Discriminant),
    Aggregate(Aggregate),
}

#[display(fmt = "{}({})", kind, argument)]
pub struct UnaryOp {
    pub kind: UnaryOpKind,
    pub argument: Operand,
}

#[display(fmt = "{}({}, {})", kind, left, right)]
pub struct BinaryOp {
    pub kind: BinaryOpKind,
    pub left: Operand,
    pub right: Operand,
}

#[display(fmt = "discriminant({})", place)]
pub struct Discriminant {
    pub place: Expression,
}

#[display(fmt = "aggregate<{}>({})", ty, "display::cjoin(operands)")]
pub struct Aggregate {
    pub ty: Type,
    pub operands: Vec<Operand>,
}

#[display(fmt = "{}({})", kind, expression)]
pub struct Operand {
    pub kind: OperandKind,
    pub expression: Expression,
}

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant, Copy)]
pub enum OperandKind {
    Copy,
    Move,
    Constant,
}
