#![no_std]
extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

pub struct B {
    inner: [A],
}

impl B {
    #[pure]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    /// Assign an ADT to a slice element directly
    #[requires(index < self.len())]
    pub fn set(&mut self, index: usize, a: A) {
        //~^ ERROR generating fold-unfold Viper statements failed
        self.inner[index] = a;
    }
}

fn main() {}
