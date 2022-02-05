pub(crate) use super::{
    super::{cfg::procedure::BasicBlockId, operations_internal::ty::Typed, Expression, Position},
    predicate::Predicate,
    rvalue::Rvalue,
};

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant)]
#[allow(clippy::large_enum_variant)]
pub enum Statement {
    Comment(Comment),
    Inhale(Inhale),
    Exhale(Exhale),
    Assert(Assert),
    FoldOwned(FoldOwned),
    UnfoldOwned(UnfoldOwned),
    JoinBlock(JoinBlock),
    SplitBlock(SplitBlock),
    MovePlace(MovePlace),
    CopyPlace(CopyPlace),
    WritePlace(WritePlace),
    WriteAddress(WriteAddress),
    Assign(Assign),
}

#[display(fmt = "// {}", comment)]
pub struct Comment {
    pub comment: String,
}

/// Inhale the permission denoted by the place.
#[display(fmt = "inhale {}", predicate)]
pub struct Inhale {
    pub predicate: Predicate,
    pub position: Position,
}

#[display(fmt = "exhale {}", predicate)]
/// Exhale the permission denoted by the place.
pub struct Exhale {
    pub predicate: Predicate,
    pub position: Position,
}

#[display(fmt = "assert {}", expression)]
/// Assert the boolean expression.
pub struct Assert {
    pub expression: Expression,
    pub position: Position,
}

#[display(fmt = "fold {}", place)]
/// Fold `OwnedNonAliased(place)`.
pub struct FoldOwned {
    pub place: Expression,
    pub condition: Option<Vec<BasicBlockId>>,
    pub position: Position,
}

#[display(fmt = "unfold {}", place)]
/// Unfold `OwnedNonAliased(place)`.
pub struct UnfoldOwned {
    pub place: Expression,
    pub condition: Option<Vec<BasicBlockId>>,
    pub position: Position,
}

#[display(fmt = "join {}", place)]
/// Join `MemoryBlock(place)`.
pub struct JoinBlock {
    pub place: Expression,
    pub condition: Option<Vec<BasicBlockId>>,
    pub position: Position,
}

#[display(fmt = "split {}", place)]
/// Split `MemoryBlock(place)`.
pub struct SplitBlock {
    pub place: Expression,
    pub condition: Option<Vec<BasicBlockId>>,
    pub position: Position,
}

#[display(fmt = "move {} ← {}", target, source)]
pub struct MovePlace {
    pub target: Expression,
    pub source: Expression,
    pub position: Position,
}

#[display(fmt = "copy {} ← {}", target, source)]
/// Copy assignment.
pub struct CopyPlace {
    pub target: Expression,
    pub source: Expression,
    pub position: Position,
}

#[display(fmt = "write_place {} := {}", target, value)]
pub struct WritePlace {
    /// A place to write the value into.
    pub target: Expression,
    pub value: Expression,
    pub position: Position,
}

#[display(fmt = "write_address {} := {}", target, value)]
pub struct WriteAddress {
    /// An adddress to write the value into.
    pub target: Expression,
    pub value: Expression,
    pub position: Position,
}

#[display(fmt = "assign {} := {}", target, value)]
pub struct Assign {
    pub target: Expression,
    pub value: Rvalue,
    pub position: Position,
}
