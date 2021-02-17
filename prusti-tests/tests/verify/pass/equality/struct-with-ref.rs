use prusti_contracts::*;

#[derive(PartialEq, Eq)]
struct A<'a> {
    i: &'a mut i32,
}

#[requires(_x == _y)]
fn test_eq(_x: &A, _y: &A) {}

fn main() {
    let mut a = 3;
    let mut b = 3;
    let x = A { i: &mut a };
    let y = A { i: &mut b };
    test_eq(&x, &y);
}
