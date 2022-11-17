#![feature(allocator_api)]

use prusti_contracts::*;

use std::vec::Vec;

#[extern_spec]
impl<T: Clone, A: std::alloc::Allocator + Clone> Clone for Vec<T, A> {
    #[ensures(true)]
    fn clone<'a>(&'a self) -> Self;
}

#[extern_spec]
impl<T> Clone for Option<T> {
    #[ensures(true)]
    fn clone(&self) -> Option::<T>
        where T: std::clone::Clone;
}

fn main() {}
