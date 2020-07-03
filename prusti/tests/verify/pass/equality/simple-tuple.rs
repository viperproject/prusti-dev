extern crate prusti_contracts;


#[derive(Clone,PartialEq,Eq)]
struct A {
    i: i32,
    t: (i32, i32),
}

#[pure]
fn get_value(x: &A) -> i32 {
    x.i + x.t.0 + x.t.1
}


#[requires="x == y"]
#[ensures="result == 2*get_value(x)"]
fn test_eq_propagation(x: &A, y: &A) -> i32 {
    get_value(x) + get_value(y)
}

fn main() {
}
