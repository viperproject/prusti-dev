use prusti_contracts::*;

#[pure]
#[requires(0 <= b && b < 100)]
#[requires(0 <= c && c < 100)]
fn test(a: bool, b: i32, c: i32) -> i32 {
    let mut x = b;
    let mut y = c;
    if a {
        x = c;
        y = b;
    }
    // x + y // TODO: PCG doesn't unpack the tuple?
    x
}

#[requires(test(false, 42, 72) == 42)]
fn main() {}
