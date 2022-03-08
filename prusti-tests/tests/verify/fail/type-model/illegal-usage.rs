extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

#[model]
struct Vec<#[concrete] i32> {
    elems: usize,
}

#[extern_spec]
impl Vec<i32> {

    #[ensures( result.model().elems == 0 )]
    fn new() -> Vec<i32>;

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

fn main() {
    let mut v = create_vec();
    add_elems(&mut v);
    assert!(v.model().elems == 2); //~ ERROR: [Prusti: invalid specification] using models in non-specification code is not allowed
    v.model().elems += 1; //~ ERROR: [Prusti: invalid specification] using models in non-specification code is not allowed


    // Nested usage in closure
    let cl = || {
        assert!(v.model().elems == 2); //~ ERROR: [Prusti: invalid specification] using models in non-specification code is not allowed
    };

    fn nested() {
        let mut v = create_vec();
        assert!(v.model().elems == 2); //~ ERROR: [Prusti: invalid specification] using models in non-specification code is not allowed
    }
}
