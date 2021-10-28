use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A;

impl A {
    #[pure]
    pub fn get(&self) -> usize {
        0
    }
}

#[pure]
pub fn test(a: A) {
    a.get();
}

fn main() {}
