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

    /// Lookup an ADT from a slice
    #[requires(index < self.len())]
    pub const fn get(&self, index: usize) -> A {
        //~^ ERROR generating fold-unfold Viper statements failed
        self.inner[index]
    }

    /// Lookup an ADT from a slice
    #[pure]
    #[requires(index < self.len())]
    pub const fn get_pure(&self, index: usize) -> A {
        //~^ ERROR generating fold-unfold Viper statements failed
        self.inner[index]
    }
}

fn main() {}
