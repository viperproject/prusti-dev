use prusti_contracts::*;

#[pure]
fn fib(n: isize) -> isize {
    if n <= 1 {
        1
    } else {
        fib(n-1) + fib(n-2)
    }
}

pub fn test1() {
    // Each call unrolls the function. Hence all assertions pass.
    assert!(fib(0) == 1);
    assert!(fib(1) == 1);
    assert!(fib(2) == 2);
    assert!(fib(3) == 3);
    assert!(fib(4) == 5);
}

pub fn test2() {
    // We unroll the function at most once, hence this fails.
    assert!(fib(4) == 5);   //~ ERROR the asserted expression might not hold
}

#[pure]
fn dummy(_n: isize, _res: isize) -> bool { true }

#[requires(
    // This is an unsound quantifier to check whether triggerring works.
    forall(|n: isize, res: isize| fib(n) == res, triggers=[(dummy(n, res),)])
)]
pub fn test3() {
    dummy(4, 5);
    assert!(fib(4) == 5);
}

fn main() {}
