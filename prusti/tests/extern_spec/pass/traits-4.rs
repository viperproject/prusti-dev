#![feature(register_tool)]
#![register_tool(prusti)]

extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

#[extern_spec]
impl<T> Vec<T> {
    #[ensures(true)]
    fn clone(&self) -> Vec::<T>
        where T: std::clone::Clone;
}

#[extern_spec]
impl<T> Option<T> {
    #[ensures(true)]
    fn clone(&self) -> Option::<T>
        where T: std::clone::Clone;
}

fn main() {}
