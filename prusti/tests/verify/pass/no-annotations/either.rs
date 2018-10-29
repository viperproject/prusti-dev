//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

extern crate prusti_contracts;

enum Either {
    Left(i32),
    Right(i32)
}

fn main() {
    let x = Either::Left(123);
}
