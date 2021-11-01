#![no_std]
extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A {
    _inner: usize,
}

#[repr(transparent)]
pub struct B {
    inner: [A],
}

impl B {
    /// Obtain a shared reference to a slice of ADTs within a slice
    #[requires(index <= self.inner.len())]
    pub fn get(&self, index: usize) -> &[A] {
        //~^ ERROR generating fold-unfold Viper statements failed
        &self.inner[0..index]
    }

    /// Obtain a shared reference to a slice of ADTs within a slice
    #[pure]
    #[requires(index <= self.inner.len())]
    pub fn get_pure(&self, index: usize) -> &[A] {
        //~^ ERROR generating fold-unfold Viper statements failed
        &self.inner[0..index]
    }
}

fn main() {}
