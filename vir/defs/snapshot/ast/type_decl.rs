use super::{expression::Expression, field::FieldDecl, ty::Type};
use crate::common::display;

#[derive_helpers]
pub enum TypeDecl {
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

#[display(fmt = "{} {{\n{}}}\n", name, "display::foreach!(\"{},\n\", fields)")]
pub struct Product {
    pub name: String,
    /// Fields.
    pub fields: Vec<FieldDecl>,
}

#[display(fmt = "{}", name)]
pub struct Sum {
    pub name: String,
    pub discriminant_bounds: Expression,
    pub discriminant_values: Vec<Expression>,
    pub variants: Vec<Product>,
}

#[display(
    fmt = "&{}{}",
    "{if *is_reference { \"\" } else { \"raw\" }}",
    target_type
)]
pub struct Pointer {
    pub is_reference: bool,
    pub target_type: Type,
}

#[display(fmt = "Array({:?}, {})", length, element_type)]
pub struct Indexed {
    pub length: Option<u64>,
    pub element_type: Type,
}
