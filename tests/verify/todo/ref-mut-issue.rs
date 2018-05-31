#![feature(nll)]

extern crate prusti_contracts;

struct T {
    val: i32
}

fn compute() -> T {
    let mut x = T { val: 11 };

    let y = &mut x;

    y.val = 22;

    // here y dies and the permission should go back to x

    x.val = 33;

    x
}

fn main() {}
