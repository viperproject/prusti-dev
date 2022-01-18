//~ ERROR consistency error in B::new: Consistency error: expected the same type, but got Snap$struct$m_A and Ref
extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

#[derive(Clone, Copy)]
pub struct B([A; 4]);

impl B {
    /// Initialization of an array holding ADTs.
    #[pure]
    pub const fn new() -> Self {
        Self([A(0), A(1), A(2), A(3)])
    }
}

fn main() {}
