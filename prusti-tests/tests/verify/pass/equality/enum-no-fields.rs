use prusti_contracts::*;

#[derive(Clone,PartialEq,Eq)]
enum A {
    U,
    V,
}

#[requires(_x == _y)]
#[ensures(result == 17)]
fn test(_x: &A, _y: &A) -> i32 {
    17
}

fn main() {
}
