extern crate prusti_contracts;

#[derive(Clone,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn get_value(_x: A) -> A {
    _x
}

fn test(_x: A) {
    let _zx = get_value(_x);
}

fn main() {
}

