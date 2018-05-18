#![feature(nll)]

extern crate prusti_contracts;

fn foo(x: ((i32, Option<(i32, i32)>), i32)) -> ((i32, Option<(i32, i32)>), i32) {
    let y = x;
    let z = x;
    y
}

fn main() {

}
