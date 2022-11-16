//! Example of program that uses a non-lexical lifetime for reference `z`

#![feature(nll)]

use prusti_contracts::*;

struct T {
    val: i32
}

fn compute(flag: bool) -> (T, T) {
    let mut x = T { val: 11 };
    let mut y = T { val: 22 };

    let z = if flag {
        &mut x
    } else {
        &mut y
    };

    z.val += 33;

    // here `z` dies and the permission should "go back" to `x` or `y`

    x.val += 44;
    y.val += 44;

    assert!(x.val == 88 || x.val == 55);
    assert!(y.val == 66 || y.val == 99);

    (x, y)
}

fn main() {}
