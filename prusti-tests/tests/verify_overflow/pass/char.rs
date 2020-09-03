extern crate prusti_contracts;

fn test_char_upperbound(x: char) {
    assert!(x as u32 <= 0x10ffffu32);
}

fn main() {}
