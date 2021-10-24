#![no_std]
extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A {
    _inner: usize,
}
pub struct B {
    inner: [A],
}

impl B {
    /// Obtain the length of a slice.
    #[pure]
    // FIXME: https://github.com/viperproject/prusti-dev/issues/718
    pub const fn len(&self) -> usize {
        //~^ ERROR unhandled verification error
        self.inner.len()
    }
}

pub fn test(b: &mut B) -> usize {
    b.len()
}

fn main() {}
