extern crate prusti_contracts;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

fn main() {
    let a = A { i: 17 };
    let b = A { i: 42 };
    assert!(a != b);
}

