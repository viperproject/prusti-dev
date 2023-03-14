// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

#[trusted]
#[requires(low(i) && low_event())]
fn print_int(i: i32) {}

fn foo(b: bool) {
    if b {
        print_int(0);
    } else {
        print_int(1);
    }
}

fn main() {}
