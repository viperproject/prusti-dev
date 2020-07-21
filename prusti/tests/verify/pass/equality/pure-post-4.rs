extern crate prusti_contracts;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
#[trusted]
#[ensures="x == result"]
fn first(x: A, y: A) -> A {
    x
}

fn main() {

    let a = A { i: 17 };
    let b = A { i: 42 };

    let u = first(a,b);
    assert!(u == a);
    
    // assert!(u == b); // fails
}

