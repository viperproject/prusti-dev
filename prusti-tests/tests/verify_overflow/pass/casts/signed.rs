use prusti_contracts::*;

pub fn i32_i64(x: i32) -> i64 {
    x as i64
}

pub fn i32_isize(x: i32) -> isize {
    x as isize
}

#[requires(x < std::i32::MAX as i64)]
#[requires(std::i32::MIN as i64 <= x)]
pub fn i64_u32(x: i64) -> i32 {
    x as i32
}

#[requires(x < std::i16::MAX as i64)]
#[requires(std::i16::MIN as i64 <= x)]
pub fn i64_i16(x: i64) -> i16 {
    x as i16
}

#[requires(x < std::i8::MAX as i64)]
#[requires(std::i8::MIN as i64 <= x)]
pub fn i64_i8(x: i64) -> i8 {
    x as i8
}

#[requires(x < std::i8::MAX as i16)]
#[requires(std::i8::MIN as i16 <= x)]
pub fn u16_i8(x: i16) -> i8 {
    x as i8
}

fn main() {}