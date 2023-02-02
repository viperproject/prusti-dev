// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

#[ensures(low(i1) && low(i2) ==> low(result))]
fn add(i1: i32, i2: i32) -> i32 {
    i1 + i2
}

#[ensures(low(result))]
fn produce_low() -> i32 {
    40
}

fn produce_high() -> i32 {
    2
}

#[requires(low(i))]
fn requires_low(i: i32) {}

fn requires_high(_i: i32) {}

fn main() {
    let i1_low = produce_low();
    let i2_low = produce_low();
    let i1_high = produce_high();
    let i2_high = produce_high();

    requires_low(add(i1_low, i2_low));
    requires_high(add(i1_low, i2_low)); // low values can be used in as high
    requires_high(add(i1_low, i2_high));
    requires_high(add(i1_high, i2_low));
    requires_high(add(i1_high, i2_high));
}
