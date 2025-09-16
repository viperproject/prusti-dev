//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(box_patterns)]

enum Either {
    Left(i32),
    Right(i32)
}

fn main() {
    let x = Either::Left(123);
}
