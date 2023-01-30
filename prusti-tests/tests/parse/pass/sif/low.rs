// compile-flags: -Psif=true

use prusti_contracts::*;

#[requires(low(n))]
fn foo(n: i32) -> i32 {
    n
}

#[ensures(low(result))]
fn bar() -> i32 {
    42
}

fn baz() -> i32 {
    let x = 1;
    let y = 2;
    prusti_assert!(low(x + y));
    x + y
}

fn main() {}
