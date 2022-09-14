pub(crate) use super::{
    expression::{BinaryOpKind, Expression, UnaryOpKind, VariableDecl},
    ty::{LifetimeConst, Type, Uniqueness},
};
use crate::common::{display, position::Position};

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant)]
#[allow(clippy::large_enum_variant)]
pub enum Rvalue {
    // Use(Use),
    Repeat(Repeat),
    Ref(Ref),
    Reborrow(Reborrow),
    // ThreadLocalRef(ThreadLocalRef),
    AddressOf(AddressOf),
    Len(Len),
    Cast(Cast),
    BinaryOp(BinaryOp),
    CheckedBinaryOp(CheckedBinaryOp),
    // NullaryOp(NullaryOp),
    UnaryOp(UnaryOp),
    Discriminant(Discriminant),
    Aggregate(Aggregate),
    // ShallowInitBox(ShallowInitBox),
}

#[display(fmt = "[{}; {}]", argument, count)]
pub struct Repeat {
    pub argument: Operand,
    /// Repetition count.
    pub count: u64,
}

#[display(fmt = "&{} {} {}", new_borrow_lifetime, uniqueness, place)]
pub struct Ref {
    pub new_borrow_lifetime: LifetimeConst,
    pub place: Expression,
    pub uniqueness: Uniqueness,
    pub lifetime_token_permission: Expression,
}

#[display(
    fmt = "&'{} {} *'{} {}",
    new_borrow_lifetime,
    uniqueness,
    deref_lifetime,
    deref_place
)]
pub struct Reborrow {
    pub new_borrow_lifetime: LifetimeConst,
    pub deref_lifetime: LifetimeConst,
    pub deref_place: Expression,
    pub uniqueness: Uniqueness,
    pub lifetime_token_permission: Expression,
}

#[display(fmt = "&raw({})", place)]
pub struct AddressOf {
    pub place: Expression,
}

#[display(fmt = "len({})", place)]
pub struct Len {
    pub place: Expression,
}

#[display(fmt = "cast({} -> {})", operand, ty)]
pub struct Cast {
    // TODO: kind: CastKind,
    pub operand: Operand,
    pub ty: Type,
}

#[display(fmt = "{}({}, {})", kind, left, right)]
pub struct BinaryOp {
    pub kind: BinaryOpKind,
    pub left: Operand,
    pub right: Operand,
}

#[display(fmt = "checked {}({}, {})", kind, left, right)]
pub struct CheckedBinaryOp {
    pub kind: BinaryOpKind,
    pub left: Operand,
    pub right: Operand,
}

#[display(fmt = "{}({})", kind, argument)]
pub struct UnaryOp {
    pub kind: UnaryOpKind,
    pub argument: Operand,
}

/// If `source_permission` is `None`, it means `write`. Otherwise, it is a
/// variable denoting the permission amount.
#[display(fmt = "discriminant({})", place)]
pub struct Discriminant {
    pub place: Expression,
    pub source_permission: Option<VariableDecl>,
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
