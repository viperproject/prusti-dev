use prusti_contracts::*;

trait A {}

impl A for i32 {}

#[trusted]
#[refine_spec(where T: A, [
    ensures(result % 2 == 0)
])]
#[refine_spec(where T: A, [
    ensures(result > 0)
])]
fn foo<T>(_x: T) -> i32 {
    42
}

fn main() {
    let result = foo(1);
    assert!(result % 2 == 0);
    assert!(result > 0);
}
