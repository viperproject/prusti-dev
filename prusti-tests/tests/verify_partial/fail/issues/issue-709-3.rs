//~ ERROR Consistency error: expected the same type, but got Snap$struct$m_A and Ref
#![no_std]
extern crate prusti_contracts;
use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

#[derive(Clone, Copy)]
pub struct B([A; 16]);

impl B {
    /// Assign an ADT to an array element directly
    #[requires(index < self.0.len())]
    pub fn set(&mut self, index: usize, a: A) {
        self.0[index] = a;
    }
}

fn main() {}
