#![feature(nll)]

use prusti_contracts::*;

struct T {
    val: i32
}

fn identity(x: &mut T) -> &mut T {
    x
}

fn main() {}
