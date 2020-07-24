extern crate prusti_contracts;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn id(_x: A) -> A {
    _x
}

#[requires="_x == _y"]
fn f(_x: A, _y: A) {
    let _z = id(_x);
    assert!(_z == id(_y));
}

fn main() {
}

