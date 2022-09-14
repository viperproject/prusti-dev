pub(crate) use super::{
    expression::Expression,
    field::FieldDecl,
    position::Position,
    ty::{GenericType, LifetimeConst, Type, Uniqueness},
    variable::VariableDecl,
};
use crate::common::display;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::From, derive_more::IsVariant, derive_more::Unwrap)]
#[allow(clippy::large_enum_variant)]
pub enum TypeDecl {
    Bool,
    Int(Int),
    Float(Float),
    TypeVar(TypeVar),
    Tuple(Tuple),
    Struct(Struct),
    Sequence(Sequence),
    Map(Map),
    Enum(Enum),
    Union(Union),
    Array(Array),
    Slice(Slice),
    Reference(Reference),
    Pointer(Pointer),
    // FnPointer,
    Never,
    // Str,
    Closure(Closure),
    // Projection(Projection),
    Unsupported(Unsupported),
    Trusted(Trusted),
}

#[display(
    fmt = "Int({},{})",
    "display::option!(lower_bound, \"{}\", \"\")",
    "display::option!(upper_bound, \" {}\", \"\")"
)]
pub struct Int {
    pub lower_bound: Option<Box<Expression>>,
    pub upper_bound: Option<Box<Expression>>,
}

#[display(
    fmt = "Float({},{})",
    "display::option!(lower_bound, \"{}\", \"\")",
    "display::option!(upper_bound, \" {}\", \"\")"
)]
pub struct Float {
    pub lower_bound: Option<Box<Expression>>,
    pub upper_bound: Option<Box<Expression>>,
}

pub struct TypeVar {
    pub name: String,
}

#[display(fmt = "({})", "display::cjoin(arguments)")]
pub struct Tuple {
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
    pub arguments: Vec<Type>,
}

#[display(fmt = "{} {{\n{}}}\n", name, "display::foreach!(\"{},\n\", fields)")]
pub struct Struct {
    pub name: String,
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
    pub structural_invariant: Option<Vec<Expression>>,
    pub fields: Vec<FieldDecl>,
    /// The size of the struct if known at compile time.
    pub size: Option<u64>,
    pub position: Position,
}

pub type DiscriminantValue = i128;
pub type DiscriminantRange = (DiscriminantValue, DiscriminantValue);

#[display(fmt = "{}", name)]
pub struct Enum {
    pub name: String,
    pub arguments: Vec<Type>,
    pub discriminant_type: Type,
    pub discriminant_bounds: Vec<DiscriminantRange>,
    pub discriminant_values: Vec<DiscriminantValue>,
    pub variants: Vec<Struct>,
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
}

#[display(fmt = "{}", name)]
pub struct Union {
    pub name: String,
    pub arguments: Vec<Type>,
    pub discriminant_type: Type,
    pub discriminant_bounds: Vec<DiscriminantRange>,
    pub discriminant_values: Vec<DiscriminantValue>,
    pub variants: Vec<Struct>,
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
}

#[display(fmt = "Array({})", element_type)]
pub struct Array {
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
    pub element_type: Type,
}

#[display(fmt = "Slice({})", element_type)]
pub struct Slice {
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
    pub element_type: Type,
}

#[display(fmt = "Sequence({})", element_type)]
pub struct Sequence {
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
    pub element_type: Type,
}

#[display(fmt = "Map({} -> {})", key_type, val_type)]
pub struct Map {
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
    pub key_type: Type,
    pub val_type: Type,
}

#[display(fmt = "&{} {}", uniqueness, target_type)]
pub struct Reference {
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
    pub uniqueness: Uniqueness,
    pub target_type: Type,
}

#[display(fmt = "*{}", target_type)]
pub struct Pointer {
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
    pub target_type: Type,
}

#[display(fmt = "{}", name)]
pub struct Closure {
    pub name: String,
    /// The tuple of captured arguments.
    pub arguments: Vec<Type>,
}

#[display(fmt = "{}", ty)]
pub struct Unsupported {
    pub ty: Type,
}

#[display(fmt = "{}", name)]
pub struct Trusted {
    pub name: String,
    pub lifetimes: Vec<LifetimeConst>,
    pub const_parameters: Vec<VariableDecl>,
}
