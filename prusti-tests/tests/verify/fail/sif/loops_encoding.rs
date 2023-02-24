// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

#[trusted]
#[requires(low(i))]
fn print(i: u32) {}

fn foo(y: u32) {
    let mut i = 0;
    while i < y + 1 {
        body_invariant!(low(i));
        i += 1;
    }
    print(i);
    print(y);
}

fn main() {}
