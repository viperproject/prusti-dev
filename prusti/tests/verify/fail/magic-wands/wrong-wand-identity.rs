#![feature(nll)]

extern crate prusti_contracts;

struct T {
    val: i32
}

#[ensures="false"] //~ ERROR
fn identity(x: &mut T) -> &mut T {
    x
}

fn main() {}
