use prusti_contracts::*;

trait A {}

#[refine_spec(where T: A, [
    ensures(true)
])]
fn foo<T>() {} //~ ERROR: Type-conditional spec refinements can only be applied to trusted functions

fn main() {}
