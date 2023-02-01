// compile-flags: -Psif=true

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
