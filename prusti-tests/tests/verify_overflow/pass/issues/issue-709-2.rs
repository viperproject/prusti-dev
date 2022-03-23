extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

#[derive(Clone, Copy)]
pub struct B([A; 16]);

impl B {
    /// Lookup an ADT from an array
    #[requires(index < self.0.len())]
    pub const fn get(&self, index: usize) -> A {
        self.0[index]
    }

    /// Lookup an ADT from an array
    #[pure]
    #[requires(index < self.0.len())]
    pub const fn get_pure(&self, index: usize) -> A {
        self.0[index]
    }
}

fn main() {}
