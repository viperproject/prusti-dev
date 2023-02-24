// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

#[requires(low(x) && low(y))]
#[ensures(result == x || result == y)]
#[ensures(low(result))]
fn loop_max(x: i32, y: i32) -> i32 {
    let mut res = x;
    while res < y {
        res += 1;
    }
    res
}

#[ensures(low(result))]
fn test(n: u32) -> u32 {
    let mut res = 0;
    while res < n {
        res += 1;
    }
    declassify!(res);
    res
}

fn main() {}
