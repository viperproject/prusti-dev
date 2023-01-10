pub(crate) use super::{
    super::{cfg::procedure::BasicBlockId, operations_internal::ty::Typed, Expression, Position},
    predicate::Predicate,
    rvalue::{Operand, Rvalue},
    ty::{LifetimeConst, Type, Uniqueness, VariantIndex},
    variable::VariableDecl,
};
use crate::common::display;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant)]
#[allow(clippy::large_enum_variant)]
pub enum Statement {
    Comment(Comment),
    OldLabel(OldLabel),
    InhalePredicate(InhalePredicate),
    ExhalePredicate(ExhalePredicate),
    InhaleExpression(InhaleExpression),
    ExhaleExpression(ExhaleExpression),
    Assume(Assume),
    Assert(Assert),
    Consume(Consume),
    Havoc(Havoc),
    GhostHavoc(GhostHavoc),
    HeapHavoc(HeapHavoc),
    FoldOwned(FoldOwned),
    UnfoldOwned(UnfoldOwned),
    FoldRef(FoldRef),
    UnfoldRef(UnfoldRef),
    JoinBlock(JoinBlock),
    JoinRange(JoinRange),
    SplitBlock(SplitBlock),
    SplitRange(SplitRange),
    ConvertOwnedIntoMemoryBlock(ConvertOwnedIntoMemoryBlock),
    RestoreMutBorrowed(RestoreMutBorrowed),
    MovePlace(MovePlace),
    CopyPlace(CopyPlace),
    WritePlace(WritePlace),
    WriteAddress(WriteAddress),
    Assign(Assign),
    GhostAssign(GhostAssign),
    SetUnionVariant(SetUnionVariant),
    // Pack(Pack),
    // Unpack(Unpack),
    RestoreRawBorrowed(RestoreRawBorrowed),
    StashRange(StashRange),
    StashRangeRestore(StashRangeRestore),
    NewLft(NewLft),
    EndLft(EndLft),
    DeadReference(DeadReference),
    DeadLifetime(DeadLifetime),
    DeadInclusion(DeadInclusion),
    LifetimeTake(LifetimeTake),
    LifetimeReturn(LifetimeReturn),
    OpenMutRef(OpenMutRef),
    OpenFracRef(OpenFracRef),
    CloseMutRef(CloseMutRef),
    CloseFracRef(CloseFracRef),
    BorShorten(BorShorten),
}

#[display(fmt = "// {}", comment)]
pub struct Comment {
    pub comment: String,
}

// A label to which it is possible to refer with `LabelledOld` expressions.
#[display(fmt = "old-label {}", name)]
pub struct OldLabel {
    pub name: String,
    pub position: Position,
}

/// Inhale the permission denoted by the place. This operation is automatically
/// managed by fold-unfold.
#[display(fmt = "inhale-pred {}", predicate)]
pub struct InhalePredicate {
    pub predicate: Predicate,
    pub position: Position,
}

#[display(fmt = "exhale-pred {}", predicate)]
/// Exhale the permission denoted by the place. This operation is automatically
/// managed by fold-unfold.
pub struct ExhalePredicate {
    pub predicate: Predicate,
    pub position: Position,
}

#[display(fmt = "consume {}", operand)]
/// Consume the operand.
pub struct Consume {
    pub operand: Operand,
    pub position: Position,
}

#[display(fmt = "havoc {}", predicate)]
/// Havoc the permission denoted by the place.
pub struct Havoc {
    pub predicate: Predicate,
    pub position: Position,
}

#[display(fmt = "ghost-havoc {}", variable)]
pub struct GhostHavoc {
    pub variable: VariableDecl,
    pub position: Position,
}

#[display(fmt = "heap-havoc")]
/// Havoc the heap.
pub struct HeapHavoc {
    pub position: Position,
}

#[display(fmt = "inhale-expr {}", expression)]
/// Inhale the boolean expression. This operation is ignored by fold-unfold.
pub struct InhaleExpression {
    pub expression: Expression,
    pub position: Position,
}

#[display(fmt = "exhale-expr {}", expression)]
/// Exhale the boolean expression. This operation is ignored by fold-unfold.
pub struct ExhaleExpression {
    pub expression: Expression,
    pub position: Position,
}

#[display(fmt = "assume {}", expression)]
/// Assume the pure boolean expression.
pub struct Assume {
    pub expression: Expression,
    pub position: Position,
}

#[display(
    fmt = "assert{} {}",
    "display::option!(condition, \"<{}>\", \"\")",
    expression
)]
/// Assert the pure boolean expression.
pub struct Assert {
    pub expression: Expression,
    pub condition: Option<BlockMarkerCondition>,
    pub position: Position,
}

#[display(
    fmt = "{}{}",
    "display::condition!(*visited, \"\", \"!\")",
    basic_block_id
)]
#[derive(PartialOrd, Ord)]
pub struct BlockMarkerConditionElement {
    pub basic_block_id: BasicBlockId,
    pub visited: bool,
}

#[display(fmt = "{}", "display::cjoin(elements)")]
#[derive(PartialOrd, Ord)]
pub struct BlockMarkerCondition {
    pub elements: Vec<BlockMarkerConditionElement>,
}

#[display(
    fmt = "fold-owned{} {}",
    "display::option!(condition, \"<{}>\", \"\")",
    place
)]
/// Fold `OwnedNonAliased(place)`.
pub struct FoldOwned {
    pub place: Expression,
    pub condition: Option<BlockMarkerCondition>,
    pub position: Position,
}

#[display(
    fmt = "unfold-owned{} {}",
    "display::option!(condition, \"<{}>\", \"\")",
    place
)]
/// Unfold `OwnedNonAliased(place)`.
pub struct UnfoldOwned {
    pub place: Expression,
    pub condition: Option<BlockMarkerCondition>,
    pub position: Position,
}

#[display(
    fmt = "fold-{}-ref{} {} {}",
    uniqueness,
    "display::option!(condition, \"<{}>\", \"\")",
    lifetime,
    place
)]
/// Fold `MutRef(place)`.
pub struct FoldRef {
    pub place: Expression,
    pub lifetime: LifetimeConst,
    pub uniqueness: Uniqueness,
    pub condition: Option<BlockMarkerCondition>,
    pub position: Position,
}

#[display(
    fmt = "unfold-{}-ref{} {} {}",
    uniqueness,
    "display::option!(condition, \"<{}>\", \"\")",
    lifetime,
    place
)]
/// Unfold `MutRef(place)`.
pub struct UnfoldRef {
    pub place: Expression,
    pub lifetime: LifetimeConst,
    pub uniqueness: Uniqueness,
    pub condition: Option<BlockMarkerCondition>,
    pub position: Position,
}

#[display(
    fmt = "join{} {}{}",
    "display::option!(condition, \"<{}>\", \"\")",
    place,
    "display::option!(enum_variant, \"[{}]\", \"\")"
)]
/// Join `MemoryBlock(place)`.
pub struct JoinBlock {
    pub place: Expression,
    pub condition: Option<BlockMarkerCondition>,
    /// If we are joining ex-enum, then we need to know for which variant.
    pub enum_variant: Option<VariantIndex>,
    pub position: Position,
}

#[display(fmt = "join-range {} {} {}", address, start_index, end_index)]
pub struct JoinRange {
    pub address: Expression,
    pub start_index: Expression,
    pub end_index: Expression,
    pub position: Position,
}

#[display(
    fmt = "split{} {}{}",
    "display::option!(condition, \"<{}>\", \"\")",
    place,
    "display::option!(enum_variant, \"[{}]\", \"\")"
)]
/// Split `MemoryBlock(place)`.
pub struct SplitBlock {
    pub place: Expression,
    pub condition: Option<BlockMarkerCondition>,
    /// If we are splitting for enum, then we need to know for which variant.
    pub enum_variant: Option<VariantIndex>,
    pub position: Position,
}

#[display(fmt = "split-range {} {} {}", address, start_index, end_index)]
pub struct SplitRange {
    pub address: Expression,
    pub start_index: Expression,
    pub end_index: Expression,
    pub position: Position,
}

/// Convert `Owned(place)` into `MemoryBlock(place)`.
#[display(
    fmt = "convert-owned-memory-block{} {}",
    "display::option!(condition, \"<{}>\", \"\")",
    place
)]
pub struct ConvertOwnedIntoMemoryBlock {
    pub place: Expression,
    pub condition: Option<BlockMarkerCondition>,
    pub position: Position,
}

/// Restore a mutably borrowed place.
#[display(
    fmt = "restore-mut-borrowed{} &{} {}",
    "display::option!(condition, \"<{}>\", \"\")",
    lifetime,
    place
)]
pub struct RestoreMutBorrowed {
    pub lifetime: LifetimeConst,
    pub place: Expression,
    pub condition: Option<BlockMarkerCondition>,
    pub position: Position,
}

#[display(fmt = "move {} ← {}", target, source)]
pub struct MovePlace {
    pub target: Expression,
    pub source: Expression,
    pub position: Position,
}

#[display(
    fmt = "copy{} {} ← {}",
    "display::option!(source_permission, \"({})\", \"\")",
    target,
    source
)]
/// Copy assignment.
///
/// If `source_permission` is `None`, it means `write`. Otherwise, it is a
/// variable denoting the permission amount.
pub struct CopyPlace {
    pub target: Expression,
    pub source: Expression,
    pub source_permission: Option<VariableDecl>,
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

#[display(fmt = "ghost-assign {} := {}", target, value)]
pub struct GhostAssign {
    pub target: Expression,
    pub value: Expression,
    pub position: Position,
}

#[display(fmt = "set-union-variant {}", variant_place)]
pub struct SetUnionVariant {
    pub variant_place: Expression,
    pub position: Position,
}

// #[display(fmt = "pack {}", place)]
// pub struct Pack {
//     pub place: Expression,
//     pub position: Position,
// }

// #[display(fmt = "unpack {}", place)]
// pub struct Unpack {
//     pub place: Expression,
//     pub position: Position,
// }

#[display(
    fmt = "restore-raw-borrowed {} --* {}",
    borrowing_place,
    restored_place
)]
pub struct RestoreRawBorrowed {
    pub borrowing_place: Expression,
    pub restored_place: Expression,
    pub position: Position,
}

#[display(
    fmt = "stash-range {} {} {} {}",
    address,
    start_index,
    end_index,
    label
)]
pub struct StashRange {
    pub address: Expression,
    pub start_index: Expression,
    pub end_index: Expression,
    pub label: String,
    pub position: Position,
}

#[display(
    fmt = "stash-range-restore {} {} {} {} → {} {}",
    old_address,
    old_start_index,
    old_end_index,
    old_label,
    new_address,
    new_start_index
)]
pub struct StashRangeRestore {
    pub old_address: Expression,
    pub old_start_index: Expression,
    pub old_end_index: Expression,
    pub old_label: String,
    pub new_address: Expression,
    pub new_start_index: Expression,
    pub position: Position,
}

#[display(fmt = "{} = newlft()", target)]
pub struct NewLft {
    pub target: VariableDecl,
    pub position: Position,
}

#[display(fmt = "endlft({})", lifetime)]
pub struct EndLft {
    pub lifetime: VariableDecl,
    pub position: Position,
}

#[display(fmt = "dead-reference({})", target)]
pub struct DeadReference {
    pub target: Expression,
    pub condition: Option<BlockMarkerCondition>,
    pub position: Position,
}

#[display(fmt = "dead-lifetime({}, {})", target, lifetime)]
pub struct DeadLifetime {
    pub target: Expression,
    pub lifetime: LifetimeConst,
    pub condition: Option<BlockMarkerCondition>,
    pub position: Position,
}

#[display(fmt = "dead_inclusion({}, {})", target, value)]
pub struct DeadInclusion {
    pub target: VariableDecl,
    pub value: VariableDecl,
    pub position: Position,
}

#[display(
    fmt = "{} := lifetime_take({}, {})",
    target,
    "display::cjoin(value)",
    lifetime_token_permission
)]
pub struct LifetimeTake {
    pub target: VariableDecl,
    pub value: Vec<VariableDecl>,
    pub lifetime_token_permission: Expression,
    pub position: Position,
}

#[display(
    fmt = "lifetime_return({}, {}, {})",
    target,
    "display::cjoin(value)",
    lifetime_token_permission
)]
pub struct LifetimeReturn {
    pub target: VariableDecl,
    pub value: Vec<VariableDecl>,
    pub lifetime_token_permission: Expression,
    pub position: Position,
}

#[display(
    fmt = "open_mut_ref({}, rd({}), {})",
    lifetime,
    lifetime_token_permission,
    place
)]
pub struct OpenMutRef {
    pub lifetime: LifetimeConst,
    pub lifetime_token_permission: Expression,
    pub place: Expression,
    pub position: Position,
}

#[display(
    fmt = "{} := open_frac_ref({}, rd({}), {})",
    predicate_permission_amount,
    lifetime,
    lifetime_token_permission,
    place
)]
pub struct OpenFracRef {
    pub lifetime: LifetimeConst,
    /// The permission amount that we get for accessing `Owned`.
    pub predicate_permission_amount: VariableDecl,
    /// The permission amount taken from the token.
    pub lifetime_token_permission: Expression,
    pub place: Expression,
    pub position: Position,
}

#[display(
    fmt = "close_mut_ref({}, rd({}), {})",
    lifetime,
    lifetime_token_permission,
    place
)]
pub struct CloseMutRef {
    pub lifetime: LifetimeConst,
    pub lifetime_token_permission: Expression,
    pub place: Expression,
    pub position: Position,
}

#[display(
    fmt = "close_frac_ref({}, rd({}), {}, {})",
    lifetime,
    lifetime_token_permission,
    place,
    predicate_permission_amount
)]
pub struct CloseFracRef {
    pub lifetime: LifetimeConst,
    /// The permission amount taken from the token.
    pub lifetime_token_permission: Expression,
    pub place: Expression,
    /// The permission amount that we get for accessing `Owned`.
    pub predicate_permission_amount: VariableDecl,
    pub position: Position,
}

#[display(
    fmt = "bor_shorten({}, {}, {}, rd({}))",
    lifetime,
    old_lifetime,
    value,
    lifetime_token_permission
)]
pub struct BorShorten {
    pub lifetime: LifetimeConst,
    pub old_lifetime: LifetimeConst,
    pub value: Expression,
    pub lifetime_token_permission: Expression,
    pub position: Position,
}
