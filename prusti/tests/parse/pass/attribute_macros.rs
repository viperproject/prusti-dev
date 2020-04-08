#![feature(attr_literals)]

extern crate prusti_contracts;

// Extend Prusti to allow writing specifications in functional style
#[requires("x > 0 && y > 0")]
#[ensures("result >= x && result >= y")]
#[ensures("result == x || result == y")]
pub fn loop_max(x: u32, y: u32) -> u32 {
    let mut r = x;
    #[invariant("r >= x")]
    #[invariant("r == x || r <= y")]
    while r < y {
        r += 1
    }
    r
}

fn main() {}
