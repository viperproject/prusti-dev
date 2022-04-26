pub(crate) use super::{
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
#[derive(derive_more::From, derive_more::IsVariant)]
#[allow(clippy::large_enum_variant)]
pub enum Statement {
    Comment(Comment),
    OldLabel(OldLabel),
    Inhale(Inhale),
    Exhale(Exhale),
    Consume(Consume),
    Assume(Assume),
    Assert(Assert),
    MovePlace(MovePlace),
    CopyPlace(CopyPlace),
    WritePlace(WritePlace),
    WriteAddress(WriteAddress),
    Assign(Assign),
    LeakAll(LeakAll),
    SetUnionVariant(SetUnionVariant),
    NewLft(NewLft),
    EndLft(EndLft),
    GhostAssignment(GhostAssignment),
    LifetimeTake(LifetimeTake),
    OpenMutRef(OpenMutRef),
    CloseMutRef(CloseMutRef),
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

#[display(fmt = "copy {} ← {}", target, source)]
/// Copy assignment.
pub struct CopyPlace {
    pub target: Expression,
    pub source: Expression,
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

#[display(fmt = "ghost-assign {} := {}", target, value)]
pub struct GhostAssignment {
    pub target: VariableDecl,
    pub value: Expression,
    pub position: Position,
}

#[display(fmt = "{} := shorten_lifetime({:?}, {})", target, value, rd_perm)]
pub struct LifetimeTake {
    pub target: VariableDecl,
    pub value: Vec<LifetimeConst>,
    pub rd_perm: u32,
    pub position: Position,
}

#[display(fmt = "open_mut_ref({}, {}, {})", lifetime, rd_perm, object)]
pub struct OpenMutRef {
    pub lifetime: LifetimeConst,
    pub rd_perm: u32,
    pub object: Expression,
    pub position: Position,
}

#[display(fmt = "close_mut_ref({}, {}, {})", lifetime, rd_perm, object)]
pub struct CloseMutRef {
    pub lifetime: LifetimeConst,
    pub rd_perm: u32,
    pub object: Expression,
    pub position: Position,
}
