extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A {
    inner: usize,
}
pub struct B {
    inner: [A],
}

impl B {
    /// Mutably reference an ADT within a slice
    #[requires(index < self.inner.len())]
    pub fn get_mut(&mut self, index: usize) -> &mut A {
        //~^ ERROR cannot generate fold-unfold Viper statements
        &mut self.inner[index]
    }
}

pub fn test(b: &mut B) {
    if b.inner.len() > 1 {
        *b.get_mut(1) = A { inner: 1 };
    }
}

fn main() {}
