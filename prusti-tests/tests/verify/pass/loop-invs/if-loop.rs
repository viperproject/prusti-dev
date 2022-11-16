use prusti_contracts::*;

struct MyStruct {
    field: i32,
}

#[requires(0 <= n)]
// Commented-out because of non-linear arithmetic.
//#[ensures(result == old(n) * (old(n) + 1) / 2)]
fn sum(n: i32) -> i32 {
    let mut res = 0;
    let mut i = 0;
    // Note: here we branch just before the loop
    if true {
        while i <= n {
            body_invariant!(n == old(n));
            body_invariant!(i <= (n + 1));
            //body_invariant!(res == (i - 1) * i / 2);
            res = res + i;
            i = i + 1;
        }
    }
    res
}

fn main() {
//  assert!(sum(100) == 5050);
//  assert!(sum(100) != 5);
//  assert!(sum(0) != 1);
//  assert!(sum(0) == 0);
//  assert!(sum(1) != 0);
//  assert!(sum(1) == 1);
}
