use prusti_contracts::*;

#[requires(0 <= n && n <= 20)]
#[trusted]
#[pure]
#[ensures(result == match n {
    0 => 0,
    1 => 1,
    _ => fib(n - 1) + fib(n - 2),
})]
fn fib(n: i32) -> i32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fib(n - 1) + fib(n - 2),
    }
}

#[requires(0 <= n && n <= 20)]
#[pure]
#[ensures(result == match n {
    0 => 0,
    1 => 1,
    _ => fib2(n - 1) + fib2(n - 2), //~ ERROR: precondition of pure function call might not hold
})]
fn fib2(n: i32) -> i32 {
    //~^ ERROR: only trusted functions can call themselves in their contracts
    match n {
        0 => 0,
        1 => 1,
        _ => fib2(n - 1) + fib2(n - 2),
    }
}

fn main() {}
