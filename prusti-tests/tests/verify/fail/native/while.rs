// compile-flags: -Pviper_backend=Lithium

use prusti_contracts::*;

const N: i32 = 10;

#[requires(i <= N)]
#[ensures(result == N)]
fn wrong_invariant(i: i32) -> i32 {
    let mut ret = i;
    while ret < N {
        body_invariant!(ret == i); //~ ERROR loop invariant might not hold
        ret += 1;
    }
    ret
}

#[requires(i <= N)]
#[ensures(result == N)] //~ ERROR might not hold
fn weak_invariant(i: i32) -> i32 {
    let mut ret = i;
    while ret < N {
        body_invariant!(ret <= N);
        ret += 1;
    }
    ret
}

fn main() {}
