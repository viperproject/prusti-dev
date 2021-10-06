use crate::common::display;

pub enum Type {
    Int,
    Bool,
    TypeVar(TypeVar),
    Struct(Struct),
    Enum(Enum),
    Array(Array),
    Slice(Slice),
    Reference(Reference),
    Pointer(Pointer),
    FnPointer,
}

pub struct TypeVar {
    pub name: String,
}

#[display(fmt = "{}<{}>", name, "display::cjoin(arguments)")]
pub struct Struct {
    pub name: String,
    /// Type arguments.
    pub arguments: Vec<Type>,
}

pub struct VariantIndex {
    pub index: String,
}

#[display(
    fmt = "{}{}<{}>",
    name,
    "display::option!(variant, \"[{}]\", \"\")",
    "display::cjoin(arguments)"
)]
pub struct Enum {
    pub name: String,
    /// Type arguments.
    pub arguments: Vec<Type>,
    /// A specific variant of the enum that this type represents.
    pub variant: Option<VariantIndex>,
}

#[display(fmt = "Array({}, {})", length, element_type)]
pub struct Array {
    pub length: usize,
    pub element_type: Box<Type>,
}

#[display(fmt = "Slice({})", element_type)]
pub struct Slice {
    pub element_type: Box<Type>,
}

#[display(fmt = "&{}", target_type)]
pub struct Reference {
    pub target_type: Box<Type>,
}

#[display(fmt = "*{}", target_type)]
pub struct Pointer {
    pub target_type: Box<Type>,
}
