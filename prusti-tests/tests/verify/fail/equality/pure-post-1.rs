use prusti_contracts::*;

// Copy is missing here
#[derive(Clone,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure] 
#[requires(_x == _y)]
#[ensures(_x == _y)]
fn get_value(_x: A, _y: A) -> A { //~ ERROR 
    _x
}

fn main() {
}
