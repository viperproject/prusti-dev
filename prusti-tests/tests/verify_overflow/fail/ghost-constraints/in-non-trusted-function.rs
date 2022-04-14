// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

trait A {}

#[ghost_constraint(T: A, [
ensures(true)
])]
fn foo<T>() {} //~ ERROR: Ghost constraints can only be used on trusted functions

fn main() {
}