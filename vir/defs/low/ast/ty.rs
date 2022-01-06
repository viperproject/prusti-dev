use crate::common::display;

#[derive_helpers]
#[derive_visitors]
#[derive(derive_more::IsVariant)]
pub enum Type {
    Int,
    Bool,
    Float(Float),
    BitVector(BitVector),
    Seq(Seq),
    Ref,
    Domain(Domain),
}

pub enum Float {
    F32,
    F64,
}

pub enum BitVector {
    BV8,
    BV16,
    BV32,
    BV64,
    BV128,
}

pub struct Seq {
    pub element_type: Box<Type>,
}

pub struct Domain {
    pub name: String,
}
