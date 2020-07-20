extern crate prusti_contracts;

#[derive(Clone,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn get_value(x: A) -> A {
    x
}

fn main() {
    let x = A { i: 17 };
 //   let y = A { i: 17 };
    let z = get_value(x);
    
//    assert!(y == z);
}

