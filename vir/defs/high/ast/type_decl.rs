use super::{expression::Expression, field::FieldDecl, ty::Type};
use crate::common::display;

#[derive_helpers]
pub enum TypeDecl {
    Bool,
    Int(Int),
    TypeVar(TypeVar),
    Tuple(Tuple),
    Struct(Struct),
    Enum(Enum),
    // Union(Union),
    Array(Array),
    // Slice(Slice),
    Reference(Reference),
    // Pointer(Pointer),
    // FnPointer,
    Never,
    // Str,
    Closure(Closure),
    // Projection(Projection),
    Unsupported(Unsupported),
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

pub struct TypeVar {
    pub name: String,
}

#[display(fmt = "({})", "display::cjoin(arguments)")]
pub struct Tuple {
    /// Type arguments.
    pub arguments: Vec<Type>,
}

#[display(fmt = "{} {{\n{}}}\n", name, "display::foreach!(\"{},\n\", fields)")]
pub struct Struct {
    pub name: String,
    // /// Type parameters.
    //
    // FIXME: Parameters are not used because we monomorphize the types when
    // encoding from MIR to high.
    //
    // pub parameters: Vec<TypeVar>,
    /// Fields.
    pub fields: Vec<FieldDecl>,
}

#[display(fmt = "{}", name)]
pub struct Enum {
    pub name: String,
    pub discriminant_bounds: Expression,
    pub discriminant_values: Vec<Expression>,
    pub variants: Vec<Struct>,
}

#[display(fmt = "Array({}, {})", length, element_type)]
pub struct Array {
    pub length: u64,
    pub element_type: Box<Type>,
}

#[display(fmt = "&{}", target_type)]
pub struct Reference {
    pub target_type: Type,
}

#[display(fmt = "{}", name)]
pub struct Closure {
    pub name: String,
}

#[display(fmt = "{}", ty)]
pub struct Unsupported {
    pub ty: Type,
}
