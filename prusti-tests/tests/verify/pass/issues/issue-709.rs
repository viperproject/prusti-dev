extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

#[derive(Clone, Copy)]
pub struct B([A; 16]);

impl B {
    #[pure]
    /// Initialization of an array holding ADTs.
    pub fn new() -> Self {
        Self([A(0); 16])
    }
}

pub fn main() {}