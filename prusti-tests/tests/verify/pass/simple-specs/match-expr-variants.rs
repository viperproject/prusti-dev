//! Example: test match expressions

use prusti_contracts::*;

#[requires(x == -42)]
#[ensures(match result { Some(..) => true, _ => false })]
fn test_match_expr(x: i32) -> Option<i32> {
    assert!(x == -42);
    Some(x)
}

fn main() {

}
