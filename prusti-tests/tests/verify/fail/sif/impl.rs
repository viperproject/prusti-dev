// compile-flags: -Psif=true

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

fn add_low_high() {
    let i1_low = produce_low();
    let i2_high = produce_high();

    requires_low(add(i1_low, i2_high)); //~ERROR precondition might not hold.
}

fn add_high_low() {
    let i1_high = produce_high();
    let i2_low = produce_low();

    requires_low(add(i1_high, i2_low)); //~ERROR precondition might not hold.
}

fn add_high_high() {
    let i1_high = produce_high();
    let i2_high = produce_high();

    requires_low(add(i1_high, i2_high)); //~ERROR precondition might not hold.
}

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
