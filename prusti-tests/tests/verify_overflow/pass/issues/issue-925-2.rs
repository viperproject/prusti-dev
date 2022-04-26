use prusti_contracts::*;

fn main() {
    let a = A::new(1);
}

#[derive(Clone, Copy)]
pub struct A {
    a: isize,
}

impl A {
    #[pure]
    #[requires(a <= isize::MAX as usize)]
    pub fn new(a: usize) -> Self {
        Self { a: a as isize }
    }
}
