use prusti_contracts::*;

/// This is a trusted procedure, so no error should be reported
#[trusted]
#[ensures(if old(x) < 0 { result == -old(x) } else { result == old(x) })]
fn abs(x: i64) -> i64 {
    x.abs()
}

/// This is a trusted procedure, so no error should be reported
#[trusted]
#[ensures(result == if old(x) == 0 { 0 } else if old(x) > 0  { 1 } else { -1 })]
fn signum(x: i64) -> i64 {
    x.signum()
}

fn main() {
    assert!(abs(0) == 0);
    assert!(abs(123) == 123);
    assert!(abs(-123) == 123);
    assert!(signum(0) == 0);
    assert!(signum(123) == 1);
    assert!(signum(-123) == -1);
}
