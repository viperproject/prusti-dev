// compile-flags: -Psif=true

use prusti_contracts::*;

#[requires(low(i))]
#[ensures(low(result))]
fn foo(i: i32) -> i32 {
    i + 42
}

#[requires(low(n))]
fn bar(n: i32) {}

#[ensures(low(result))]
fn baz() -> i32 {
    42
}

fn main() {
    let i = baz();
    let j = foo(i);
    bar(j);
}
