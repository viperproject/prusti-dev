extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

#[model]
struct Vec<i32> {
    elems: usize,
}

#[extern_spec]
impl Vec<i32> {

    #[ensures( result.model().elems == 0 )]
    fn new() -> Vec<i32>;

    #[requires( self.model().elems > 0 )]
    #[requires( 0 <= index && index <= self.model().elems )]
    #[ensures( self.model().elems == old(self.model().elems) - 1 )]
    fn remove(&mut self, index: usize) -> i32;

    #[ensures( self.model().elems == 1 + old(self.model().elems) )]
    fn push(&mut self, val: i32);
}

#[ensures( result.model().elems == 0 )]
fn create_vec() -> Vec<i32> {
    Vec::new()
}

#[requires( v.model().elems == 0 )]
#[ensures( v.model().elems == 2 )]
fn add_elems(v: &mut Vec<i32>) {
    v.push(1);
    v.push(1);
}

#[requires( v.model().elems == 2 )]
#[ensures( v.model().elems == 0 )]
fn remove_elems(v: &mut Vec<i32>) {
    v.remove(0);
    v.remove(0);
}

fn main() {
    let mut v = create_vec();
    add_elems(&mut v);
    remove_elems(&mut v);
}
