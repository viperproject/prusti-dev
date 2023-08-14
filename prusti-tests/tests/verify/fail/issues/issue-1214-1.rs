use prusti_contracts::*;

#[pure]
#[ensures(result == 0)]
fn f(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        g(n - 1)
    }
}

#[pure]
#[ensures(result == 0)]
fn g(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        f(n - 1)
    }
}

fn test() {
    assert!(f(0) == 0);
    assert!(g(0) == 0);
    assert!(f(1) == 0);
    assert!(g(1) == 0);
    assert!(f(2) == 0);
    assert!(g(2) == 0);
    assert!(f(3) == 0);
    assert!(g(3) == 0);
    assert!(false); //~ ERROR the asserted expression might not hold
}

fn main() {}
