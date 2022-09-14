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
    MemoryBlockHeapRange(MemoryBlockHeapRange),
    MemoryBlockHeapDrop(MemoryBlockHeapDrop),
    OwnedNonAliased(OwnedNonAliased),
    OwnedRange(OwnedRange),
    OwnedSet(OwnedSet),
    UniqueRef(UniqueRef),
    UniqueRefRange(UniqueRefRange),
    FracRef(FracRef),
    FracRefRange(FracRefRange),
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

#[display(
    fmt = "MemoryBlockHeapRange({}, {}, {}, {})",
    address,
    size,
    start_index,
    end_index
)]
pub struct MemoryBlockHeapRange {
    pub address: Expression,
    pub size: Expression,
    pub start_index: Expression,
    pub end_index: Expression,
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

/// A range of owned predicates of a specific type. `start_index` is inclusive
/// and `end_index` is exclusive.
#[display(fmt = "OwnedRange({}, {}, {})", address, start_index, end_index)]
pub struct OwnedRange {
    pub address: Expression,
    pub start_index: Expression,
    pub end_index: Expression,
    pub position: Position,
}

/// A set of owned predicates of a specific type.
#[display(fmt = "OwnedSet({})", set)]
pub struct OwnedSet {
    pub set: Expression,
    pub position: Position,
}

/// A unique reference predicate of a specific type.
#[display(fmt = "UniqueRef({}, {})", lifetime, place)]
pub struct UniqueRef {
    pub lifetime: LifetimeConst,
    pub place: Expression,
    pub position: Position,
}

/// A range of unique reference predicates of a specific type. `start_index` is
/// inclusive and `end_index` is exclusive.
#[display(
    fmt = "UniqueRefRange({}, {}, {}, {})",
    lifetime,
    address,
    start_index,
    end_index
)]
pub struct UniqueRefRange {
    pub lifetime: LifetimeConst,
    pub address: Expression,
    pub start_index: Expression,
    pub end_index: Expression,
    pub position: Position,
}

/// A shared reference predicate of a specific type.
#[display(fmt = "FracRef({}, {})", lifetime, place)]
pub struct FracRef {
    pub lifetime: LifetimeConst,
    pub place: Expression,
    pub position: Position,
}

/// A range of shared reference predicates of a specific type. `start_index` is
/// inclusive and `end_index` is exclusive.
#[display(
    fmt = "FracRefRange({}, {}, {}, {})",
    lifetime,
    address,
    start_index,
    end_index
)]
pub struct FracRefRange {
    pub lifetime: LifetimeConst,
    pub address: Expression,
    pub start_index: Expression,
    pub end_index: Expression,
    pub position: Position,
}
