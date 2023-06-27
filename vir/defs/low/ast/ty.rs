use crate::common::display;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::IsVariant)]
pub enum Type {
    Int,
    Bool,
    Perm,
    Float(Float),
    BitVector(BitVector),
    Seq(Seq),
    Set(Set),
    MultiSet(MultiSet),
    Map(Map),
    Ref,
    Domain(Domain),
}

pub enum Float {
    F32,
    F64,
}

pub enum BitVector {
    #[display(fmt = "S{}", "self")]
    Signed(BitVectorSize),
    #[display(fmt = "U{}", "self")]
    Unsigned(BitVectorSize),
}

pub enum BitVectorSize {
    BV8,
    BV16,
    BV32,
    BV64,
    BV128,
}

#[display(fmt = "Seq({})", element_type)]
pub struct Seq {
    pub element_type: Box<Type>,
}

#[display(fmt = "Set({})", element_type)]
pub struct Set {
    pub element_type: Box<Type>,
}

#[display(fmt = "MultiSet({})", element_type)]
pub struct MultiSet {
    pub element_type: Box<Type>,
}

#[display(fmt = "D({})", name)]
pub struct Domain {
    pub name: String,
}

#[display(fmt = "Map({} -> {})", key_type, val_type)]
pub struct Map {
    pub key_type: Box<Type>,
    pub val_type: Box<Type>,
}
