// compile-flags: -Psif=true

use prusti_contracts::*;

#[requires(low(i))]
#[ensures(low(result))]
fn foo(i: i32) -> i32 {
    i + 42
}

#[requires(low(n))]
fn bar(n: i32) {}

fn baz_safe() -> i32 {
    42
}

fn main() {
    let i = baz_safe();
    let j = foo(i); //~ERROR precondition might not hold
    bar(j);
}
