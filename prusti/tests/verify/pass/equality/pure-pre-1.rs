extern crate prusti_contracts;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
#[requires="x == y"]
fn get_value(x: A, y: A) -> A {
    x
}

fn main() {
}

