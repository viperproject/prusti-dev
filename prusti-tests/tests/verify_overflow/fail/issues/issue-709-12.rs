extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

#[derive(Clone, Copy)]
pub struct B(pub [A; 16]);

impl B {
    /// Mutably slice into an array of ADTs
    #[requires(index <= self.0.len())]
    #[ensures(result.len() == index)]
    pub fn get_mut(&mut self, index: usize) -> &mut [A] {
        &mut self.0[0..index] //~ ERROR mutably slicing is not fully supported yet
    }
}

pub fn test(b: &mut B) {
    b.get_mut(1)[0] = A(1);
}

fn main() {}
