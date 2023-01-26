use prusti_contracts::*;
use std::slice::Iter;

#[model]
struct Iter<'a, #[generic] T: Copy> {
    position: usize,
}

#[extern_spec]
impl<T: Copy + PartialEq> [T] {
    #[ensures( result.model().position == 0 )]
    fn iter(&self) -> std::slice::Iter<'_, T>;
}

fn verify_slice_iter(slice: &[i32]) {
    let iter = slice.iter();
}

fn main() {}
