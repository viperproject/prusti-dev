pub(crate) use super::{
    super::{operations_internal::ty::Typed, Expression, Position},
    predicate::Predicate,
};

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant)]
pub enum Statement {
    Comment(Comment),
    Inhale(Inhale),
    Exhale(Exhale),
    FoldOwned(FoldOwned),
    UnfoldOwned(UnfoldOwned),
    JoinBlock(JoinBlock),
    SplitBlock(SplitBlock),
    MovePlace(MovePlace),
    CopyPlace(CopyPlace),
    WritePlace(WritePlace),
    WriteAddress(WriteAddress),
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

#[display(fmt = "fold {}", place)]
/// Fold `OwnedNonAliased(place)`.
pub struct FoldOwned {
    pub place: Expression,
    pub position: Position,
}

#[display(fmt = "unfold {}", place)]
/// Unfold `OwnedNonAliased(place)`.
pub struct UnfoldOwned {
    pub place: Expression,
    pub position: Position,
}

#[display(fmt = "join {}", place)]
/// Join `MemoryBlock(place)`.
pub struct JoinBlock {
    pub place: Expression,
    pub position: Position,
}

#[display(fmt = "split {}", place)]
/// Split `MemoryBlock(place)`.
pub struct SplitBlock {
    pub place: Expression,
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
