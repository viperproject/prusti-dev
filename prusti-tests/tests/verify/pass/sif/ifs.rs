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

#[requires(low(l))]
#[ensures(low(result))]
fn foo(b: bool, l: i32) -> i32 {
    let res;
    if b {
        res = l + 3;
    } else {
        res = l - 3;
    }
    if b {
        res - 3
    } else {
        res + 3
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

    let res = choose(false, h, l);
    prusti_assert!(low(res));
}
