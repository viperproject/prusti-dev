#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_must_use)]

use prusti_contracts::*;

fn main() {
    let mut x = 5;
    let mut y = 42;

    std::mem::swap(&mut x, &mut y);

    assert!(42 == x);
    assert!(5 == y);
}
