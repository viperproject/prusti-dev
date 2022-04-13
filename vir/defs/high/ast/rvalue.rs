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
    // Use(Use),
    // Repeat(Repeat),
    Ref(Ref),
    // ThreadLocalRef(ThreadLocalRef),
    AddressOf(AddressOf),
    // Len(Len),
    // Cast(Cast),
    BinaryOp(BinaryOp),
    // CheckedBinaryOp(CheckedBinaryOp),
    // NullaryOp(NullaryOp),
    UnaryOp(UnaryOp),
    Discriminant(Discriminant),
    Aggregate(Aggregate),
    // ShallowInitBox(ShallowInitBox),
}

#[display(fmt = "ref {}", place)]
pub struct Ref {
    pub place: Expression,
    pub lifetime_name: String,
    pub is_mut: bool,
    pub rd_perm: u32,
    pub target: Expression,
}

#[display(fmt = "&raw({})", place)]
pub struct AddressOf {
    pub place: Expression,
}

#[display(fmt = "{}({}, {})", kind, left, right)]
pub struct BinaryOp {
    pub kind: BinaryOpKind,
    pub left: Operand,
    pub right: Operand,
}

#[display(fmt = "{}({})", kind, argument)]
pub struct UnaryOp {
    pub kind: UnaryOpKind,
    pub argument: Operand,
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
