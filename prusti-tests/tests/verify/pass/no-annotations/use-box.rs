#![feature(box_patterns)]

fn use_box(x: Box<i32>) -> i32 {
    *x
}

fn main() {}
