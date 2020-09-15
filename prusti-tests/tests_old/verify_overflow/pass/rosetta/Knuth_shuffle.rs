//! An adaptation of the example from
//! https://rosettacode.org/wiki/Knuth_shuffle#Rust
//!
//! Changes:
//!
//! +   Monomorphised types.
//! +   Wrapped built-in types and functions.
//! +   Rewrote loops into supported shape (while bool with no break, continue, or return).
//! +   Replaced ``println!`` with calling trusted functions.
//! +   Moved constants into variables.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Absence of overflows.

use prusti_contracts::*;

pub struct VecWrapper<T>{
    v: Vec<T>
}

impl<T> VecWrapper<T> {

    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        VecWrapper{ v: Vec::new() }
    }

    #[trusted]
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, value: T) {
        self.v.push(value);
    }

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires(0 <= index_a && index_a < self.len())]
    #[requires(0 <= index_b && index_b < self.len())]
    #[ensures(self.len() == old(self.len()))]
    pub fn swap(&mut self, index_a: usize, index_b: usize) {
        self.v.swap(index_a, index_b);
    }
}

//extern crate rand;

//use rand::Rng;

struct ThreadRngWrapper {}

impl ThreadRngWrapper {
    #[trusted]
    #[requires(low < high)]
    #[ensures(low <= result && result < high)]
    fn gen_range(&mut self, low: usize, high: usize) -> usize {
        unimplemented!();
    }
}

#[trusted]
fn thread_rng() -> ThreadRngWrapper {
    unimplemented!();
}

fn knuth_shuffle<T>(v: &mut VecWrapper<T>) {
    let mut rng = thread_rng();
    let l = v.len();

    let mut n = 0;
    let bgn = 0;
    while n < l {
        body_invariant!(n < l);
        body_invariant!(n >= 0);
        body_invariant!(bgn == 0);
        body_invariant!(l == v.len());
        let i = rng.gen_range(bgn, l - n);
        v.swap(i, l - n - 1);
        n += 1;
    }
}

use std::fmt::Debug;

#[trusted]
fn print_vector_before<T: Debug>(v: &mut VecWrapper<T>) {
    println!("before: {:?}", v.v);
}

#[trusted]
fn print_vector_after<T: Debug>(v: &mut VecWrapper<T>) {
    println!("after:  {:?}", v.v);
}

fn test() {
    let mut v = VecWrapper::new();
    let mut i = 0;
    while i < 10 {
        v.push(i);
    }

    print_vector_before(&mut v);
    knuth_shuffle(&mut v);
    print_vector_after(&mut v);
}

fn main() {}
