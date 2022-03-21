#![feature(allocator_api)]

use prusti_contracts::*;
use std::vec::Vec;
use std::option::Option;

#[extern_spec]
impl<T> Option<T> {
    #[pure]
    #[ensures(matches!(*self, Some(_)) == result)]
    pub fn is_some(&self) -> bool;

    #[pure]
    #[ensures(self.is_some() ==> !result)]
    #[ensures(!self.is_some() ==> result)]
    pub fn is_none(&self) -> bool;

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T;
}

#[extern_spec]
impl<T> Vec<T> {
    #[ensures(result.len() == 0)]
    fn new() -> Vec::<T>;
}

#[extern_spec]
impl<T, A: std::alloc::Allocator> Vec<T, A> {
    #[pure]
    fn len(&self) -> usize;

    #[ensures(self.len() == old(self.len()) + 1)]
    fn push(&mut self, value: T);

    #[ensures(self.len() == 0)]
    fn clear(&mut self);

    #[ensures(old(self.len()) == 0 ==> result.is_none())]
    #[ensures(old(self.len()) > 0 ==> result.is_some())]
    #[ensures(old(self.len()) > 0 ==> self.len() == old(self.len()) - 1)]
    pub fn pop(&mut self) -> Option<T>;

    #[ensures(self.len() == old(self.len()) + other.len())]
    pub fn append(&mut self, other: &mut Vec<T, A>);
}

fn main() {
    let mut v = Vec::new();
    v.push(2);
    v.push(3);
    v.push(5);
    assert!(v.len() == 3);
    v.pop();
    assert!(v.len() == 2);
    v.pop();
    v.pop();
    assert!(v.pop().is_none());
}
