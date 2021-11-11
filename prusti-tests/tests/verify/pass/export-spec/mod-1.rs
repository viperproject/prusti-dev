extern crate prusti_contracts;
use prusti_contracts::*;

#[export_spec(::)]
mod internal {
    #[ensures(*a == old(*b) && *b == old(*a))]
    fn swap(a: &mut i32, b: &mut i32) {
        std::mem::swap(a, b);
    }
}

fn main() {
    let mut x = 5;
    let mut y = 42;

    internal::swap(&mut x, &mut y);

    assert!(42 == x);
    assert!(5 == y);
}