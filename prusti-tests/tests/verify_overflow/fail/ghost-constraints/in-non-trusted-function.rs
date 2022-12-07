// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

trait A {}

#[refine_spec(where T: A [
	ensures(true)
])]
fn foo<T>() {} //~ ERROR: Ghost constraints can only be used on trusted functions

fn main() {
}
