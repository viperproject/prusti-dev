use crate::common::display;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::IsVariant, derive_more::Unwrap)]
pub enum Type {
    /// Mathematical boolean that corresponds to Viper's Bool.
    MBool,
    /// Mathematical integer that corresponds to Viper's Int.
    MInt,
    /// Mathematical floats that corresponds to Viper's Float.
    MFloat32,
    MFloat64,
    Lifetime,
    /// Rust's Bool allocated on the Viper heap.
    Bool,
    /// Rust's Int allocated on the Viper heap.
    Int(Int),
    Float(Float),
    TypeVar(TypeVar),
    Tuple(Tuple),
    Struct(Struct),
    Enum(Enum),
    Union(Union),
    Array(Array),
    Slice(Slice),
    Reference(Reference),
    Pointer(Pointer),
    FnPointer,
    Never,
    Str,
    Closure(Closure),
    FunctionDef(FunctionDef),
    Projection(Projection),
    Unsupported(Unsupported),
}

#[derive(Copy)]
pub enum Int {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    Char,
    /// Used for ghost and mathematical integers.
    Unbounded,
}

pub enum Float {
    F32,
    F64,
}

#[display(fmt = "{}", name)]
pub struct LifetimeConst {
    pub name: String,
}

#[display(fmt = "Lifetime")]
pub struct Lifetime {}
impl Default for Lifetime {
    fn default() -> Self {
        Self::new()
    }
}

#[display(fmt = "{}", name)]
pub struct GenericType {
    pub name: String,
}

#[derive_helpers]
#[derive(derive_more::Unwrap)]
pub enum TypeVar {
    LifetimeConst(LifetimeConst),
    GenericType(GenericType),
}

#[display(fmt = "({})", "display::cjoin(arguments)")]
pub struct Tuple {
    /// Type arguments.
    pub arguments: Vec<Type>,
}

#[display(fmt = "{}<{}>", name, "display::cjoin(arguments)")]
pub struct Struct {
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
pub struct Enum {
    pub name: String,
    /// Type arguments.
    pub arguments: Vec<Type>,
    /// A specific variant of the enum that this type represents.
    pub variant: Option<VariantIndex>,
}

#[display(fmt = "{}<{}>", name, "display::cjoin(arguments)")]
pub struct Union {
    pub name: String,
    /// Type arguments.
    pub arguments: Vec<Type>,
    /// A specific field of the union that this type represents.
    pub variant: Option<VariantIndex>,
}

#[display(fmt = "Array({}, {})", length, element_type)]
pub struct Array {
    pub length: u64,
    pub element_type: Box<Type>,
}

#[display(fmt = "Slice({})", element_type)]
pub struct Slice {
    pub element_type: Box<Type>,
}

#[derive(Copy, derive_more::IsVariant)]
pub enum Uniqueness {
    Unique,
    Shared,
}

#[display(fmt = "&{} {} {}", lifetime, uniqueness, target_type)]
pub struct Reference {
    pub lifetime: LifetimeConst,
    pub uniqueness: Uniqueness,
    pub target_type: Box<Type>,
}

#[display(fmt = "*{}", target_type)]
pub struct Pointer {
    pub target_type: Box<Type>,
}

#[display(fmt = "{}", name)]
pub struct Closure {
    pub name: String,
    // /// Type arguments.
    // FIXME: We are currently ignoring type arguments.
    // pub arguments: Vec<Type>,
}

#[display(fmt = "{}", name)]
pub struct FunctionDef {
    pub name: String,
    // /// Type arguments.
    // FIXME: We are currently ignoring type arguments.
    // pub arguments: Vec<Type>,
}

#[display(fmt = "{}<{}>", name, "display::cjoin(arguments)")]
pub struct Projection {
    pub name: String,
    /// Type arguments.
    pub arguments: Vec<Type>,
}

#[display(fmt = "{}", name)]
pub struct Unsupported {
    pub name: String,
}
