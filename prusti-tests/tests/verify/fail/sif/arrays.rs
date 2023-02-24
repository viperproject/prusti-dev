// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

#[requires(forall(|i: usize| 0 <= i && i < ts.len() ==> low(ts[i])))]
#[ensures(low(result))]
fn sum_array_low(ts: &[i32]) -> i32 {
    let mut i = 0;
    let mut res = 0;

    while i < ts.len() {
        res += ts[i];
        i += 1;
    }

    res
}

#[ensures(forall(|i: usize| 0 <= i && i < ts.len() ==> low(ts[i])) ==> low(result))]
fn sum_array(ts: &[i32]) -> i32 {
    let mut i = 0;
    let mut res = 0;

    while i < ts.len() {
        res += ts[i];
        i += 1;
    }

    res
}

#[ensures(low(result))]
fn produce_low() -> i32 {
    42
}

#[ensures(forall(|i: usize| 0 <= i && i < array.len() ==> low(array[i])))]
fn fill_with_low(array: &mut [i32]) {
    let mut i = 0;
    while i < array.len() {
        array[i] = produce_low();
        i += 1;
    }
}

fn produce_high() -> i32 {
    12
}

fn foo() {
    let mut array = [1, 2, 3, 4, 5];
    fill_with_low(&mut array);

    array[2] = produce_high();

    let res2 = sum_array(&array);
    prusti_assert!(low(res2)); //~ERROR the asserted expression might not hold
}

fn main() {
    let mut array = [1, 2, 3, 4, 5];
    fill_with_low(&mut array);

    array[2] = produce_high();

    let res1 = sum_array_low(&array); //~ERROR precondition might not hold
}
