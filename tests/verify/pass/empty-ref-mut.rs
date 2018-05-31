#![feature(nll)]

extern crate prusti_contracts;

struct T;

fn compute() -> T {
    let mut x = T;

    let y = &mut x;

    x
}

fn main() {}
