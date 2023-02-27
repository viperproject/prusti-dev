// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

#[trusted]
#[requires(low(i))]
fn print(i: u32) {}

#[requires(low(y))]
#[requires(low_event())]
fn foo(y: u32) {
    let mut i = 0;
    while i < y {
        body_invariant!(low(i));
        i += 1;
    }
    print(i);
}

fn bar(x: u32) -> u32 {
    let mut i = 0;
    while i < x {
        i += 1;
    }
    i
}

fn main() {}
