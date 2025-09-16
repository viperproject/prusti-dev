//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(box_patterns)]

fn use_box(x: Box<i32>) -> i32 {
    *x
}

fn main() {}
