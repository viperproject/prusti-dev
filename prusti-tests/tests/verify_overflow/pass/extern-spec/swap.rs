#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_must_use)]

extern crate prusti_contracts;
use prusti_contracts::*;

#[extern_spec]
mod std {
    mod mem {
        use prusti_contracts::*;

        #[ensures(*a == old(*b) && *b == old(*a))]
        pub fn swap<T: std::cmp::PartialEq + Copy>(a: &mut T, b: &mut T);
    }
}

fn main() {
    let mut x = 5;
    let mut y = 42;

    std::mem::swap(&mut x, &mut y);

    assert!(42 == x);
    assert!(5 == y);
}
