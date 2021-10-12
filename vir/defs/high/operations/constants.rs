use super::super::ast::{
    expression::*,
    position::Position,
    ty::{Int, Type},
};

macro derive_from_into_primitive($ty: ty, $variant: ident) {
    impl From<$ty> for ConstantValue {
        fn from(value: $ty) -> Self {
            Self::$variant(value.into())
        }
    }
}
macro derive_from_into_string($ty: ty) {
    impl From<$ty> for ConstantValue {
        fn from(value: $ty) -> Self {
            Self::BigInt(value.to_string())
        }
    }
}
macro derive_from($ty: ty, $vir_ty: expr) {
    impl From<$ty> for Constant {
        fn from(value: $ty) -> Self {
            Self {
                value: value.into(),
                ty: $vir_ty,
                position: Position::default(),
            }
        }
    }
    impl From<$ty> for Expression {
        fn from(value: $ty) -> Self {
            Self::Constant(value.into())
        }
    }
}

derive_from_into_primitive!(bool, Bool);
derive_from!(bool, Type::Bool);
derive_from_into_primitive!(i8, Int);
derive_from!(i8, Type::Int(Int::I8));
derive_from_into_primitive!(i16, Int);
derive_from!(i16, Type::Int(Int::I16));
derive_from_into_primitive!(i32, Int);
derive_from!(i32, Type::Int(Int::I32));
derive_from_into_primitive!(i64, Int);
derive_from!(i64, Type::Int(Int::I64));
derive_from_into_string!(i128);
derive_from!(i128, Type::Int(Int::I128));
derive_from_into_string!(isize);
derive_from!(isize, Type::Int(Int::Isize));
derive_from_into_primitive!(u8, Int);
derive_from!(u8, Type::Int(Int::U8));
derive_from_into_primitive!(u16, Int);
derive_from!(u16, Type::Int(Int::U16));
derive_from_into_primitive!(u32, Int);
derive_from!(u32, Type::Int(Int::U32));
derive_from_into_string!(u64);
derive_from!(u64, Type::Int(Int::U64));
derive_from_into_string!(u128);
derive_from!(u128, Type::Int(Int::U128));
derive_from_into_string!(usize);
derive_from!(usize, Type::Int(Int::Usize));
impl From<char> for ConstantValue {
    fn from(value: char) -> Self {
        let value: u128 = value.into();
        Self::BigInt(value.to_string())
    }
}
derive_from!(char, Type::Int(Int::Char));
