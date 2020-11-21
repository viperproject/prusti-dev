use prusti_contracts::*;

#[requires(x < std::i32::MAX as i64)]
pub fn i64_u32_max(x: i64) -> i32 {
    x as i32  //~ ERROR value might not fit into the target type.
}

#[requires(x < std::i16::MAX as i64)]
pub fn i64_i16_max(x: i64) -> i16 {
    x as i16  //~ ERROR value might not fit into the target type.
}

#[requires(x < std::i8::MAX as i64)]
pub fn i64_i8_max(x: i64) -> i8 {
    x as i8  //~ ERROR value might not fit into the target type.
}

#[requires(x < std::i8::MAX as i16)]
pub fn u16_i8_max(x: i16) -> i8 {
    x as i8  //~ ERROR value might not fit into the target type.
}

#[requires(std::i32::MIN as i64 <= x)]
pub fn i64_u32_min(x: i64) -> i32 {
    x as i32  //~ ERROR value might not fit into the target type.
}

#[requires(std::i16::MIN as i64 <= x)]
pub fn i64_i16_min(x: i64) -> i16 {
    x as i16  //~ ERROR value might not fit into the target type.
}

#[requires(std::i8::MIN as i64 <= x)]
pub fn i64_i8_min(x: i64) -> i8 {
    x as i8  //~ ERROR value might not fit into the target type.
}

#[requires(std::i8::MIN as i16 <= x)]
pub fn u16_i8_min(x: i16) -> i8 {
    x as i8  //~ ERROR value might not fit into the target type.
}

fn main() {}