extern crate prusti_contracts;

#[requires="0 <= n"]
#[ensures="result == old(n) * (old(n) + 1) / 2"]
fn sum(n: i32) -> i32 {
    let mut res = 0;
    let mut i = 0;
    // Note: here we use `n`, not `old(n)`
    #[invariant="i <= (n + 1)"]
    #[invariant="res == (i - 1) * i / 2"]
    while i <= n {
        res = res + i;
        i = i + 1;
    }
    res
}

fn main() {
    assert!(sum(100) == 5050);
    assert!(sum(100) != 5);
    assert!(sum(0) != 1);
    assert!(sum(0) == 0);
    assert!(sum(1) != 0);
    assert!(sum(1) == 1);
}
