// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

struct Point {
    x: i32,
    y: i32,
}

#[ensures(low(old(pt.x)) ==> low(*result))]
#[after_expiry(result => pt.x == *before_expiry(result))]
fn get_mut_x<'a>(pt: &'a mut Point) -> &'a mut i32 {
    &mut pt.x
}

#[trusted]
#[ensures(low(result))]
fn produces_low() -> i32 {
    12
}

#[trusted]
#[requires(low(n))]
fn requires_low(n: i32) {}

fn main() {
    let mut p = Point {
        x: produces_low(),
        y: 42,
    };
    {
        let x = get_mut_x(&mut p);
        requires_low(*x);
        *x = 19;
    }
    prusti_assert!(p.x == 19);
}
