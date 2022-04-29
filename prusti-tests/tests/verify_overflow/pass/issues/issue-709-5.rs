extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

#[derive(Clone, Copy)]
pub struct B(pub [A; 16]);

impl B {
    /// Obtain a shared reference an ADT within an array
    #[requires(index < self.0.len())]
    pub const fn get(&self, index: usize) -> &A {
        &self.0[index]
    }

    /// Obtain a shared reference an ADT within an array
    #[pure]
    #[requires(index < self.0.len())]
    pub const fn get_pure(&self, index: usize) -> &A {
        &self.0[index]
    }
}

fn main() {}
