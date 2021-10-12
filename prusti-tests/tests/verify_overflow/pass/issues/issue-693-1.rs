use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A;

impl A {
    #[pure]
    pub fn get(&self) -> A {
        A
    }
}

#[pure]
pub fn test(a: A) -> A {
    a.get().get()
}

fn main() {}
