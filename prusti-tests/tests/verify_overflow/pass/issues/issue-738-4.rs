use prusti_contracts::*;

fn main() {
    bar(1, 1);
    bar(1, 2);
    baz(1, 1);
    baz(1, 2);
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct A {
    a: usize
}

#[pure]
pub fn foo(a: usize) -> A {
    A { a }
}

/// Test surjectivity
#[pure]
#[requires(a == b ==> foo(a) == foo(b))]
pub fn bar(a: usize, b: usize) {}

/// Test injectivity
#[pure]
#[requires(foo(a) == foo(b) ==> a == b)]
pub fn baz(a: usize, b: usize) {}
