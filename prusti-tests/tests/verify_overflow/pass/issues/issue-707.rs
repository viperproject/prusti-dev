use prusti_contracts::*;

#[derive(Clone,Copy)]
pub struct A {
    _inner: usize,
}

#[derive(Clone,Copy)]
pub struct B {
    inner: A,
}

impl B {
    #[pure]
    pub fn get(&self) -> A {
        self.inner
    }
}

pub fn test(b: &B) -> A {
    b.get()
}

fn main() {}
