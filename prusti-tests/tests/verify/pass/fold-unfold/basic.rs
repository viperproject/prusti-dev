extern crate prusti_contracts;

pub fn empty() {}

pub fn local_pure() {
    let mut x = 4;
    x += 1;
    assert!(x == 5);
}

#[ensures="result == x + 1"]
pub fn argument_pure(x: u32) -> u32 {
    x + 1
}

fn main() {}
