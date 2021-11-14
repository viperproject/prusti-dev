extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

#[derive(Clone, Copy)]
pub struct B {
    inner: [A; 4]
}

impl B {
    /// Obtain the length of an ADT array.
    #[pure]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }
}

fn main() {}
