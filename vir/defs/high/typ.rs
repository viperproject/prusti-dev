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
}

pub struct TypeVar {
    pub name: String,
}

pub struct Struct {
    pub name: String,
    /// Type arguments.
    pub arguments: Vec<Type>,
}

pub struct VariantIndex {
    pub index: String,
}

pub struct Enum {
    pub name: String,
    /// Type arguments.
    pub arguments: Vec<Type>,
    /// A specific variant of the enum that this type represents.
    pub variant: Option<VariantIndex>,
}

pub struct Array {
    pub length: usize,
    pub element_type: Box<Type>,
}

pub struct Slice {
    pub element_type: Box<Type>,
}

pub struct Reference {
    pub target_type: Box<Type>,
}

pub struct Pointer {
    pub target_type: Box<Type>,
}
