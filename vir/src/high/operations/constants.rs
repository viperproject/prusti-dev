use super::super::ast::{
    expression::*,
    position::Position,
    ty::{Float, Int, Type},
};
use crate::common::constants::{derive_from, derive_from_into_primitive, derive_from_into_string};

derive_from_into_primitive!(ConstantValue, bool, Bool);
derive_from!(Constant, Expression, bool, Type::Bool);
derive_from_into_primitive!(ConstantValue, i8, Int);
derive_from!(Constant, Expression, i8, Type::Int(Int::I8));
derive_from_into_primitive!(ConstantValue, i16, Int);
derive_from!(Constant, Expression, i16, Type::Int(Int::I16));
derive_from_into_primitive!(ConstantValue, i32, Int);
derive_from!(Constant, Expression, i32, Type::Int(Int::I32));
derive_from_into_primitive!(ConstantValue, i64, Int);
derive_from!(Constant, Expression, i64, Type::Int(Int::I64));
derive_from_into_string!(ConstantValue, i128);
derive_from!(Constant, Expression, i128, Type::Int(Int::I128));
derive_from_into_string!(ConstantValue, isize);
derive_from!(Constant, Expression, isize, Type::Int(Int::Isize));
derive_from_into_primitive!(ConstantValue, u8, Int);
derive_from!(Constant, Expression, u8, Type::Int(Int::U8));
derive_from_into_primitive!(ConstantValue, u16, Int);
derive_from!(Constant, Expression, u16, Type::Int(Int::U16));
derive_from_into_primitive!(ConstantValue, u32, Int);
derive_from!(Constant, Expression, u32, Type::Int(Int::U32));
derive_from_into_string!(ConstantValue, u64);
derive_from!(Constant, Expression, u64, Type::Int(Int::U64));
derive_from_into_string!(ConstantValue, u128);
derive_from!(Constant, Expression, u128, Type::Int(Int::U128));

derive_from!(Constant, Expression, f32, Type::Float(Float::F32));
derive_from_into_string!(ConstantValue, f32);
derive_from!(Constant, Expression, f64, Type::Float(Float::F64));
derive_from_into_string!(ConstantValue, f64);

derive_from_into_string!(ConstantValue, usize);
derive_from!(Constant, Expression, usize, Type::Int(Int::Usize));
impl From<char> for ConstantValue {
    fn from(value: char) -> Self {
        let value: u128 = value.into();
        Self::BigInt(value.to_string())
    }
}
derive_from!(Constant, Expression, char, Type::Int(Int::Char));
