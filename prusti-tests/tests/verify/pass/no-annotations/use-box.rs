//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

fn use_box(x: Box<i32>) -> i32 {
    *x
}

fn main() {}
