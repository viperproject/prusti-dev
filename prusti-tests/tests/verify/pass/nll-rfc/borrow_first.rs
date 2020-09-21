//! An adaptation of the example from Matsakis
//! [blog](http://smallcultfollowing.com/babysteps/blog/2018/06/15/mir-based-borrow-check-nll-status-update/)
//! that illustrates differences between Rust 2018 NLL and Polonius.
//!
//! Changes:
//!
//! +   Rewrote to remove a return statement.
//! +   Wrapped built-in types and functions.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   Absence of overflows.

// This is currently needed for importing specifications.
use prusti_contracts::*;

/// A struct that wraps a built-in vector for signed 32-bit integers.
pub struct VecWrapperI32{
    v: Vec<i32>
}

impl VecWrapperI32 {

    // Trusted functions are assumed to be correct. This allows attaching specifications to
    // existing functions.
    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        VecWrapperI32{ v: Vec::new() }
    }

    // Pure functions can be used in specifications.
    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn borrow(&mut self, index: usize) -> &mut i32 {
        &mut self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(self.lookup(index) == value)]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() && i != index) ==>
                    self.lookup(i) == old(self.lookup(i))))]
    pub fn store(&mut self, index: usize, value: i32) {
        self.v[index] = value;
    }

    #[trusted]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.lookup(old(self.len())) == value)]
    #[ensures(forall(|i: usize| (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))))]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }

    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    #[ensures(result < 18446744073709551615)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

}

#[pure]
fn some_condition(r: &i32) -> bool {
    *r > 0
}


#[requires(vec.len() > 0)]
fn foo(vec: &mut VecWrapperI32) -> &mut i32 {
    let r = vec.borrow(0);
    if some_condition(r) {
        r
    } else {
        vec.push(5);
        let last = vec.len()-1;
        vec.borrow(last)
    }
}

fn main() {}
