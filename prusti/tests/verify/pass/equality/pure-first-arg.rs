extern crate prusti_contracts;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn get_value(x: A, y: A) -> A {
    x
}

fn main() {

    let a = A { i: 17 };
    let b = A { i: 19 };
    let x = get_value(a, b);

    assert!(x == a);
}

