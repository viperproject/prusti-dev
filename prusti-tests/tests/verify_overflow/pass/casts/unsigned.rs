use prusti_contracts::*;

pub fn u32_u64(x: u32) -> u64 {
    x as u64
}

pub fn u32_usize(x: u32) -> usize {
    x as usize
}

#[requires(x < std::u32::MAX as u64)]
pub fn u64_u32(x: u64) -> u32 {
    x as u32
}

#[requires(x < std::u16::MAX as u64)]
pub fn u64_u16(x: u64) -> u16 {
    x as u16
}

#[requires(x < std::u8::MAX as u64)]
pub fn u64_u8(x: u64) -> u8 {
    x as u8
}

#[requires(x < std::u8::MAX as u16)]
pub fn u16_u8(x: u16) -> u8 {
    x as u8
}

fn main() {}