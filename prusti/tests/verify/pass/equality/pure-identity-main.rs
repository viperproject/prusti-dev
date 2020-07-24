extern crate prusti_contracts;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn get_value(_x: A) -> A {
    _x
}

fn main() {
    let _x = A { i: 17 };
    let _y = A { i: 17 };
    let _z = get_value(_x);
    assert!(_y == _z);
}

