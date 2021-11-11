extern crate prusti_contracts;
use prusti_contracts::*;


#[export_spec(::)]
#[ensures(*a == old(*b) && *b == old(*a))]
pub fn swap(a: &mut i32, b: &mut i32) {
    std::mem::swap(a, b);
}

fn main() {
    let mut x = 5;
    let mut y = 42;

    swap(&mut x, &mut y);

    assert!(42 == x);
    assert!(5 == y);
}