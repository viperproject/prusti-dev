#![no_std]
extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

#[derive(Clone, Copy)]
pub struct B(pub [A; 16]);

impl B {
    /// Mutably slice into an array of ADTs
    #[requires(index <= self.0.len())]
    pub fn get_mut(&mut self, index: usize) -> &mut [A] {
        &mut self.0[0..index]
    }
}

pub fn test(b: &mut B) {
    //~^ ERROR generating fold-unfold Viper statements failed
    b.get_mut(1)[0] = A(1);
}

fn main() {}
