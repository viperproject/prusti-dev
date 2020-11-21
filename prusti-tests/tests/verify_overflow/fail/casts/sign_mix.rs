use prusti_contracts::*;

pub fn u64_u32(x: u64) -> i32 {
    x as i32  //~ ERROR value might not fit into the target type.
}

pub fn u64_i16(x: u64) -> i16 {
    x as i16  //~ ERROR value might not fit into the target type.
}

pub fn u64_i8(x: u64) -> i8 {
    x as i8  //~ ERROR value might not fit into the target type.
}

pub fn u16_i8(x: u16) -> i8 {
    x as i8  //~ ERROR value might not fit into the target type.
}

#[requires(0 <= x)]
pub fn i64_u32_max(x: i64) -> u32 {
    x as u32  //~ ERROR value might not fit into the target type.
}

#[requires(0 <= x)]
pub fn i64_u16_max(x: i64) -> u16 {
    x as u16  //~ ERROR value might not fit into the target type.
}

#[requires(0 <= x)]
pub fn i64_u8_max(x: i64) -> u8 {
    x as u8  //~ ERROR value might not fit into the target type.
}

#[requires(0 <= x)]
pub fn i16_u8_max(x: i16) -> u8 {
    x as u8  //~ ERROR value might not fit into the target type.
}

#[requires(x < std::u32::MAX as i64)]
pub fn i64_u32_min(x: i64) -> u32 {
    x as u32  //~ ERROR value might not fit into the target type.
}

#[requires(x < std::u16::MAX as i64)]
pub fn i64_u16_min(x: i64) -> u16 {
    x as u16  //~ ERROR value might not fit into the target type.
}

#[requires(x < std::u8::MAX as i64)]
pub fn i64_u8_min(x: i64) -> u8 {
    x as u8  //~ ERROR value might not fit into the target type.
}

#[requires(x < std::u8::MAX as i16)]
pub fn i16_u8_min(x: i16) -> u8 {
    x as u8  //~ ERROR value might not fit into the target type.
}

fn main() {}