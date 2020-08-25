#![feature(register_tool)]
#![register_tool(prusti)]
#![feature(type_ascription)]
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
        pub fn swap(a: &mut i32, b: &mut i32);
    }
}

fn main() {
    let mut x = 5;
    let mut y = 42;

    std::mem::swap(&mut x, &mut y);

    assert!(42 == x);
    assert!(5 == y);
}
