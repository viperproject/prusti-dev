use crate::common::display;

pub enum Type {
    /// Primitive (mathematical) integer.
    Int,
    /// Primitive (mathematical) bool.
    Bool,
    /// Type variable.
    TypeVar(TypeVar),
    /// A type with fields.
    Product(Product),
    /// A type with different variants.
    Sum(Sum),
    /// A type that also includes an address.
    Pointer(Pointer),
    /// A type that allows access by indexing.
    Indexed(Indexed),
}

pub struct TypeVar {
    pub name: String,
}

#[display(fmt = "{}<{}>", name, "display::cjoin(arguments)")]
pub struct Product {
    pub name: String,
    /// Type arguments.
    pub arguments: Vec<Type>,
}

#[derive(derive_more::From)]
pub struct VariantIndex {
    pub index: String,
}

#[display(
    fmt = "{}{}<{}>",
    name,
    "display::option!(variant, \"[{}]\", \"\")",
    "display::cjoin(arguments)"
)]
pub struct Sum {
    pub name: String,
    /// Type arguments.
    pub arguments: Vec<Type>,
    /// A specific variant of the enum that this type represents.
    pub variant: Option<VariantIndex>,
}

#[display(fmt = "&{}", target_type)]
pub struct Pointer {
    pub is_reference: bool,
    pub target_type: Box<Type>,
}

#[display(fmt = "Array({:?}, {})", length, element_type)]
pub struct Indexed {
    pub length: Option<u64>,
    pub element_type: Box<Type>,
}
