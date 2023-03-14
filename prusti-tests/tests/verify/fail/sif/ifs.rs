// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

#[requires(low(l))]
#[ensures(!b ==> low(result))]
fn choose(b: bool, h: i32, l: i32) -> i32 {
    if b {
        h
    } else {
        l
    }
}

#[requires(low(l1) && low(l2))]
#[ensures(low(result))] //~EROOR postcondition might not hold.
fn choose2(b: bool, l1: i32, l2: i32) -> i32 {
    if b {
        l1
    } else {
        l2
    }
}

fn produce_high() -> i32 {
    42
}

#[ensures(low(result))]
fn produce_low() -> i32 {
    12
}

fn main() {
    let l = produce_low();
    let h = produce_high();

    let res = choose(true, h, l);
    prusti_assert!(low(res)); //~ERROR the asserted expression might not hold
}
