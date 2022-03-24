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
    pub const fn len(&self) -> usize {
        self.inner.len()
    }
}

pub fn test(b: &mut B) -> usize {
    b.len()
}

fn main() {}
