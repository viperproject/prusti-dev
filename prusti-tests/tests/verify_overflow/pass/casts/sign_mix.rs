use prusti_contracts::*;

pub fn u32_i64(x: u32) -> i64 {
    x as i64
}

pub fn u32_isize(x: u32) -> isize {
    x as isize
}

#[requires(x < std::i32::MAX as u64)]
pub fn u64_u32(x: u64) -> i32 {
    x as i32
}

#[requires(x < std::i16::MAX as u64)]
pub fn u64_i16(x: u64) -> i16 {
    x as i16
}

#[requires(x < std::i8::MAX as u64)]
pub fn u64_i8(x: u64) -> i8 {
    x as i8
}

#[requires(x < std::i8::MAX as u16)]
pub fn u16_i8(x: u16) -> i8 {
    x as i8
}

#[requires(x < std::u32::MAX as i64)]
#[requires(0 <= x)]
pub fn i64_u32(x: i64) -> u32 {
    x as u32
}

#[requires(x < std::u16::MAX as i64)]
#[requires(0 <= x)]
pub fn i64_u16(x: i64) -> u16 {
    x as u16
}

#[requires(x < std::u8::MAX as i64)]
#[requires(0 <= x)]
pub fn i64_u8(x: i64) -> u8 {
    x as u8
}

#[requires(x < std::u8::MAX as i16)]
#[requires(0 <= x)]
pub fn i16_u8(x: i16) -> u8 {
    x as u8
}

fn main() {}