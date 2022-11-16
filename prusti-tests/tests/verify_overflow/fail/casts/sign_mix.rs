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

fn preserve_sign() {
    assert!(5u8 as i128 == 5i128);
    assert!(5u16 as i128 == 5i128);
    assert!(5u32 as i128 == 5i128);
    assert!(5u64 as i128 == 5i128);
    assert!(5i128 as i128 == 5i128);

    assert!(5u8 as u128 == 5u128);
    assert!(5u16 as u128 == 5u128);
    assert!(5u32 as u128 == 5u128);
    assert!(5u64 as u128 == 5u128);
    assert!(5i128 as u128 == 5u128);

    assert!(5i8 as i128 == 5i128);
    assert!(5i16 as i128 == 5i128);
    assert!(5i32 as i128 == 5i128);
    assert!(5i64 as i128 == 5i128);
    assert!(5i128 as i128 == 5i128);

    assert!(-5i8 as i128 == -5i128);
    assert!(-5i16 as i128 == -5i128);
    assert!(-5i32 as i128 == -5i128);
    assert!(-5i64 as i128 == -5i128);
    assert!(-5i128 as i128 == -5i128);

    assert!(
        -5i8 as u128 //~ ERROR value might not fit into the target type.
        == 5u128
    );
}

fn main() {}