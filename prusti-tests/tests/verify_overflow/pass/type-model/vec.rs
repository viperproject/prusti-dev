// ignore-test: This test currently fails because the model is not copy
// This is due to the use of the type param A: std::alloc::Allocator
// Actually this type param should nt be a problem because A does not appear in any model field
// but the Copy trait is not derived correctly for the generated model.

#![feature(allocator_api)]
use prusti_contracts::*;

use std::vec::Vec;
use std::alloc::Global;

#[model]
struct Vec<#[generic] T, #[generic] A: std::alloc::Allocator> {
    elems: usize,
}

#[extern_spec]
impl<T> Vec<T, Global> {
    #[ensures( result.model().elems == 0 )]
    fn new() -> Vec<T>;
}

#[extern_spec]
impl<T, A: std::alloc::Allocator> Vec<T, A> {

    #[requires( self.model().elems > 0 )]
    #[requires( 0 <= index && index <= self.model().elems )]
    #[ensures( self.model().elems == old(self.model().elems) - 1 )]
    fn remove(&mut self, index: usize) -> T;

    #[ensures( self.model().elems == 1 + old(self.model().elems) )]
    fn push(&mut self, val: T);
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
