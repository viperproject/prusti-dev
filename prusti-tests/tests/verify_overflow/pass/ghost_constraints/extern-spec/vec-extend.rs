// ignore-test: Currently fails because generics in extern trait impls are not supported TODO hansenj
use prusti_contracts::*;

#[extern_spec]
impl<T> std::vec::Vec<T> {
    #[ensures(result.len() == 0)]
    fn new() -> std::vec::Vec::<T>;

    #[pure]
    fn len(&self) -> usize;

    #[ensures(self.len() == old(self.len()) + 1)]
    fn push(&mut self, value: T);
}

use std::iter::ExactSizeIterator;
#[extern_spec]
impl<T> Extend<T> for Vec<T> {
    #[ghost_constraint(I: ExactSizeIterator, [
        ensures(self.len() == old(self.len()) + iter.len())
    ])]
    fn extend<I>(&mut self, iter: I) where I: IntoIterator<Item = T>;
}

fn main() {
    let mut v1: Vec<i32> = Vec::new();
    v1.push(1);
    assert!(v1.len() == 1);

    let mut v2: Vec<i32> = Vec::new();
    v2.push(1);
    v2.push(2);
    assert!(v2.len() == 2);

    v1.extend(v2);
    assert!(v1.len() == 3);
}