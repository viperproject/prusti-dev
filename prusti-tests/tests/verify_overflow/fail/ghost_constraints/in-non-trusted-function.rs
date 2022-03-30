// Note: For now, it is completely fine to _declare_ a ghost constraint on a non-trusted function
// since resolving happens for specific callsites. That is, without the call in main, this
// file verifies.
use prusti_contracts::*;

trait A {}
impl A for i32 {} // TODO hansenj: Check/comment that this impl is needed!

#[ghost_constraint(T: A, [
ensures(true)
])]
fn foo<T>() {} //~ ERROR: Ghost constraints can only be used on trusted functions

fn main() {
    foo::<i32>();
}