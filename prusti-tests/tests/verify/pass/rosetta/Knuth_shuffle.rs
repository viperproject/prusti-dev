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

use prusti_contracts::*;

pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        VecWrapperI32{ v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }

    #[trusted]
    #[requires(0 <= index_a && index_a < self.len())]
    #[requires(0 <= index_b && index_b < self.len())]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(self.lookup(index_a) == old(self.lookup(index_b)))]
    #[ensures(self.lookup(index_b) == old(self.lookup(index_a)))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() && i != index_a && i != index_b) ==>
                    self.lookup(i) == old(self.lookup(i))))]
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

fn knuth_shuffle(v: &mut VecWrapperI32) {
    let mut rng = thread_rng();
    let l = v.len();

    let mut n = 0;
    let bgn = 0;
    while n < l {
        body_invariant!( 0 <= n && n < l);
        body_invariant!(bgn == 0);
        body_invariant!(l == v.len());
        let i = rng.gen_range(bgn, l - n);
        v.swap(i, l - n - 1);
        n += 1;
    }
}

#[trusted]
fn print_vector_before(v: &mut VecWrapperI32) {
    println!("before: {:?}", v.v);
}

#[trusted]
fn print_vector_after(v: &mut VecWrapperI32) {
    println!("after:  {:?}", v.v);
}

fn test() {
    let mut v = VecWrapperI32::new();
    let mut i = 0;
    while i < 10 {
        v.push(i);
        i += 1;
    }

    print_vector_before(&mut v);
    knuth_shuffle(&mut v);
    print_vector_after(&mut v);
}

fn main(){}
