// TODO hansenj: Parser error
// TODO hansenj: Disallow associated types
use prusti_contracts::*;

trait A { type Item; }

impl A for i32 {
    type Item = i32;
}

#[ghost_constraint(where T: A<Item = i32> , [
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
    let result = foo(1);
    assert!(result > 0);
}
