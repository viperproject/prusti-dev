#![feature(box_patterns)]

enum Either {
    Left(i32),
    Right(i32)
}

fn main() {
    let x = Either::Left(123);
}
