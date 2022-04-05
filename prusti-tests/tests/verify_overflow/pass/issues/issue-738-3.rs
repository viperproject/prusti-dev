use prusti_contracts::*;

#[requires(test(1).a == 1)]
fn main() {}

#[derive(Clone, Copy)]
pub struct A {
    a: usize
}

#[pure]
#[requires(a <= isize::MAX as usize)]
#[ensures(result.a <= isize::MAX as usize)]
pub fn test(a: usize) -> A {
    A { a: a as isize as usize as isize as usize }
}
