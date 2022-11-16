use prusti_contracts::*;

#[pure]
fn test_minus_i32(x: i32) -> i32 {
    -x //~ ERROR negate with overflow
}

#[pure]
fn test_minus_i64(x: i64) -> i64 {
    -x //~ ERROR negate with overflow
}

#[pure]
fn test_minus_isize(x: isize) -> isize {
    -x //~ ERROR negate with overflow
}

fn main() {}
