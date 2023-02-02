// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

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
