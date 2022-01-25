//ignore-test: Extern specs for different generics not supported
extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

#[model]
struct Vec<i32> {
    last_pushed: i32,
}

#[model]
struct Vec<u32> {
    last_pushed: i32,
}

#[extern_spec]
impl Vec<i32> {
    #[ensures( result.model().last_pushed == -1 )]
    fn new() -> Vec<i32>;

    #[ensures( self.model().last_pushed == val )]
    fn push(&mut self, val: i32);
}

#[extern_spec]
impl Vec<u32> {
    #[ensures( result.model().last_pushed == -1 )]
    fn new() -> Vec<u32>;

    #[ensures( self.model().last_pushed == val as i32)]
    fn push(&mut self, val: u32);
}

fn main() {
    let mut v_i32: Vec<i32> = Vec::new();
    let mut v_u32: Vec<u32> = Vec::new();

    v_i32.push(42);
    v_u32.push(43);

    assert!(v_i32.model().last_pushed == 42);
    assert!(v_u32.model().last_pushed == 43);
}
