use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A;

impl A {
    #[pure]
    pub fn get(&self) -> A {
        A
    }

    #[pure]
    pub fn len(&self) -> usize {
        0
    }
}

#[pure]
pub fn test(a: A) -> usize {
    a.get().len()
}

fn main() {}
