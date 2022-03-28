#![feature(allocator_api)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_must_use)]

use prusti_contracts::*;

use std::vec::Vec;

#[extern_spec]
impl<T, A: std::alloc::Allocator + Clone> Clone for Vec<T, A> {
    #[ensures(true)]
    fn clone(&self) -> std::vec::Vec::<T>
        where T: std::clone::Clone;
}

#[extern_spec]
impl<T> Clone for Option<T> {
    #[ensures(true)]
    fn clone(&self) -> Option::<T>
        where T: std::clone::Clone;
}

fn main() {}
