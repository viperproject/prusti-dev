#![feature(nll)]

extern crate prusti_contracts;

struct T {
    val: i32
}

#[ensures="false"]
fn identity(x: &mut T) -> &mut T { //~ ERROR
    x
}

fn main() {}
