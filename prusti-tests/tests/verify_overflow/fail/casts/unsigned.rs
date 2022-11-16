use prusti_contracts::*;

pub fn u64_u32(x: u64) -> u32 {
    x as u32  //~ ERROR value might not fit into the target type.
}

pub fn u64_u16(x: u64) -> u16 {
    x as u16  //~ ERROR value might not fit into the target type.
}

pub fn u64_u8(x: u64) -> u8 {
    x as u8  //~ ERROR value might not fit into the target type.
}

pub fn u16_u8(x: u16) -> u8 {
    x as u8  //~ ERROR value might not fit into the target type.
}

fn main() {}