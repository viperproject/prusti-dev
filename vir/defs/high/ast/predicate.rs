pub(crate) use super::super::{
    ast::{expression::Expression, position::Position, ty::LifetimeConst},
    operations_internal::ty::Typed,
};

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant)]
pub enum Predicate {
    LifetimeToken(LifetimeToken),
    MemoryBlockStack(MemoryBlockStack),
    MemoryBlockStackDrop(MemoryBlockStackDrop),
    MemoryBlockHeap(MemoryBlockHeap),
    MemoryBlockHeapDrop(MemoryBlockHeapDrop),
    OwnedNonAliased(OwnedNonAliased),
}

#[display(fmt = "acc(LifetimeToken({}), {})", lifetime, permission)]
pub struct LifetimeToken {
    pub lifetime: LifetimeConst,
    pub permission: Expression,
    pub position: Position,
}

/// A memory block on the stack allocated with `StorageLive`.
///
/// Splitting an joining is managed automatically by the fold-unfold algorithm.
/// That is why it uses places.
///
/// Note: After fold-unfold, this predicate is replaced with predicate
/// `MemoryBlock`. We keep two kinds of predicates initially to simplify
/// fold-unfold algorithm.
#[display(fmt = "MemoryBlockStack({}, {})", place, size)]
pub struct MemoryBlockStack {
    pub place: Expression,
    pub size: Expression,
    pub position: Position,
}

/// A permission to deallocate a (precisely) matching `MemoryBlockStack`.
#[display(fmt = "MemoryBlockStackDrop({}, {})", place, size)]
pub struct MemoryBlockStackDrop {
    pub place: Expression,
    pub size: Expression,
    pub position: Position,
}

/// A memory block on the heap.
///
/// Splitting an joining is managed manually by the user. That is why it uses
/// addresses.
///
/// Note: After fold-unfold, this predicate is replaced with predicate
/// `MemoryBlock`. We keep two kinds of predicates initially to simplify
/// fold-unfold algorithm.
#[display(fmt = "MemoryBlockHeap({}, {})", address, size)]
pub struct MemoryBlockHeap {
    pub address: Expression,
    pub size: Expression,
    pub position: Position,
}

/// A permission to deallocate a (precisely) matching `MemoryBlockHeap`.
#[display(fmt = "MemoryBlockHeapDrop({}, {})", address, size)]
pub struct MemoryBlockHeapDrop {
    pub address: Expression,
    pub size: Expression,
    pub position: Position,
}

/// A non-aliased owned predicate of a specific type.
#[display(fmt = "OwnedNonAliased({})", place)]
pub struct OwnedNonAliased {
    pub place: Expression,
    pub position: Position,
}
