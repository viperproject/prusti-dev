#![feature(attr_literals)]

use prusti_contracts::*;

// Extend Prusti to allow writing specifications in functional style
#[requires(x > 0 && y > 0)]
#[ensures(result >= x && result >= y)]
#[ensures(result == x || result == y)]
pub fn loop_max(x: u32, y: u32) -> u32 {
    let mut r = x;
    while r < y {
        body_invariant!(r >= x);
        body_invariant!(r == x || r <= y);
        r += 1
    }
    r
}

fn main() {}
