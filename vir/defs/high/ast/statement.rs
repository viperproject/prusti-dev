pub(crate) use super::{
    super::cfg::procedure::BasicBlockId,
    expression::Expression,
    position::Position,
    predicate::Predicate,
    rvalue::{Operand, Rvalue},
    ty::{LifetimeConst, Type},
    variable::VariableDecl,
};
use crate::common::display;
use std::collections::BTreeSet;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant, derive_more::Unwrap)]
#[allow(clippy::large_enum_variant)]
pub enum Statement {
    Comment(Comment),
    OldLabel(OldLabel),
    Inhale(Inhale),
    Exhale(Exhale),
    Consume(Consume),
    Havoc(Havoc),
    Assume(Assume),
    Assert(Assert),
    LoopInvariant(LoopInvariant),
    MovePlace(MovePlace),
    CopyPlace(CopyPlace),
    WritePlace(WritePlace),
    WriteAddress(WriteAddress),
    Assign(Assign),
    LeakAll(LeakAll),
    SetUnionVariant(SetUnionVariant),
    NewLft(NewLft),
    EndLft(EndLft),
    DeadLifetime(DeadLifetime),
    DeadInclusion(DeadInclusion),
    LifetimeTake(LifetimeTake),
    LifetimeReturn(LifetimeReturn),
    ObtainMutRef(ObtainMutRef),
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

#[display(fmt = "assume {}", expression)]
/// Assume the boolean expression.
pub struct Assume {
    pub expression: Expression,
    pub position: Position,
}

#[display(fmt = "assert {}", expression)]
/// Assert the boolean expression.
pub struct Assert {
    pub expression: Expression,
    pub position: Position,
}

#[display(
    fmt = "loop-invariant (\n{}{})",
    "display::foreach!(\"    {}\n\", maybe_modified_places)",
    "display::foreach!(\"    {}\n\", functional_specifications)"
)]
/// The loop invariant.
pub struct LoopInvariant {
    pub loop_head: BasicBlockId,
    /// A block dominated by the loop head that has the loop head as a
    /// successor.
    pub back_edges: Vec<BasicBlockId>,
    /// Places that are potentially modified inside the loop body.
    ///
    /// If the place is definitely initialized, we havoc `OwnedNonAliased`
    /// predicate. If the place is maybe uninitialized, we havoc `MemoryBlock`
    /// predicate.
    ///
    /// Note that for soundness we have to havoc all potentially modified
    /// memory, which means that we have to havoc all potentially aliased
    /// memory.
    pub maybe_modified_places: Vec<Predicate>,
    pub functional_specifications: Vec<Expression>,
    pub position: Position,
}

#[display(fmt = "move {} ← {}", target, source)]
/// Move assignment.
///
/// In Viper, it would correspond to calling the following method:
///
/// ```viper
/// method move_place$T(
///     target_place: Place,
///     target_address: Address,
///     target_value: Snap$T,
///     source_place: Place,
///     source_address: Address,
///     source_value: Snap$T,
/// )
///     requires MemoryBlock(compute_address(target_place, target_address), size_of::<T>())
///     requires OwnedNonAliased$T(source_place, source_address, source_value)
///     requires source_value == target_value
///     ensures OwnedNonAliased$T(target_place, target_address, source_value)
///     ensures MemoryBlock(compute_address(source_place, source_address), size_of::<T>())
///     ensures MemoryBlock$bytes(compute_address(source_place, source_address), size_of::<T>()) == to_bytes$T(source_value)
/// {
///     unfold OwnedNonAliased$T(source_place, source_address, source_value)
///     write_place$T(target_place, target_address, source_value)
/// }
/// ```
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
/// Initialization of a place with a given constant.
///
/// In Viper, it would correspond to calling the following method:
///
/// ```viper
/// method write_place$T(place: Place, root_address: Address, value: Snap$T)
///     requires MemoryBlock(compute_address(place, root_address), size_of::<T>())
///     ensures OwnedNonAliased$T(place, root_address, value)
/// {
///     write_address$T(compute_address(place, root_address), value)
///     fold OwnedNonAliased$T(place, root_address, value)
/// }
/// ```
pub struct WritePlace {
    /// A place to write the value into.
    pub target: Expression,
    pub value: Expression,
    pub position: Position,
}

#[display(fmt = "write_address {} := {}", target, value)]
/// Initialization of a memory location with a given constant.
///
/// In Viper, it would correspond to calling the following method:
///
/// ```viper
/// method write_address$T(address: Address, value: Snap$T)
///     requires MemoryBlock(address, size_of::<T>())
///     ensures MemoryBlock(address, size_of::<T>())
///     ensures MemoryBlock$bytes(address, size_of::<T>()) == Snap$T$to_bytes(value)
/// ```
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

#[display(fmt = "leak-all")]
#[derive(Default)]
/// Tells fold-unfold to leak all predicates. This marks the end of the
/// unwinding path.
pub struct LeakAll {}

#[display(fmt = "set-union-variant {}", variant_place)]
pub struct SetUnionVariant {
    pub variant_place: Expression,
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

#[display(fmt = "dead-lifetime({})", lifetime)]
pub struct DeadLifetime {
    pub lifetime: LifetimeConst,
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

#[display(fmt = "obtain_mut_ref({}, {})", place, lifetime)]
pub struct ObtainMutRef {
    pub place: Expression,
    pub lifetime: LifetimeConst,
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
