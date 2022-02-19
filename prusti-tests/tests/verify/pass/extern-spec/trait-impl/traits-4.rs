#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_must_use)]

extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

#[extern_spec]
impl<T> Clone for Vec<T> {
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
