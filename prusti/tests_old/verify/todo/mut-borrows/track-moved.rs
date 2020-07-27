//! Motivating example for traking "moved paths" in the fold/unfold state

#![feature(nll)]

extern crate prusti_contracts;

struct T {
    val: i32
}

fn compute(mut x: T, mut y: T, flag: bool) -> (T, T) {
    let z = if flag {
        &mut x
    } else {
        &mut y
    };

    z.val += 1;

    (x, y)
}

fn main() {}
