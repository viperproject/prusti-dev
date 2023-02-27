// compile-flags: -Pviper_backend=Lithium

use prusti_contracts::*;

const N: i32 = 10;

#[requires(i <= N)]
#[ensures(result == N)]
fn test(i: i32) -> i32 {
    let mut ret = i;
    while ret < N {
        body_invariant!(ret < N);
        ret += 1;
    }
    ret
}

fn main() {
    assert!(test(3) == N);
}
