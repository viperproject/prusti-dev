use prusti_contracts::*;

#[pure]
pub fn foo(inner: &[usize; 4]) -> bool {
    true
}

#[pure]
pub fn bar(inner: &[usize; 4]) -> bool {
    foo(inner);
    foo(inner);
    true
}

fn main() {}
