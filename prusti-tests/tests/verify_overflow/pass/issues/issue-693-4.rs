use prusti_contracts::*;

#[derive(Clone, Copy)]
pub struct A(usize);

impl A {
    #[pure]
    pub fn len(&self) -> usize {
        0
    }
}

#[pure]
pub fn a() -> A {
    A(0)
}

#[pure]
pub fn test() -> usize {
    a().len()
}

fn main() {}
