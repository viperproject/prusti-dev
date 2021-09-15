//! Example: test match expressions

use prusti_contracts::*;

#[requires(x == -42)]
#[ensures(match result { -84 => true, 123 | 456 => false, _ => false })]
fn test_match_expr(x: i32) -> i32 {
    assert!(x == -42);
    x * 2
}

#[requires(x == -42)]
#[ensures(match result { Some(k) => k == -42, _ => false })]
fn test_match_option_expr(x: i32) -> Option<i32> {
    assert!(x == -42);
    Some(x)
}

fn main() {

}
