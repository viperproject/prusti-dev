//! Example: test match expressions

extern crate prusti_contracts;

#[requires="x == -42"]
#[ensures="match result { -84 => true, 123 | 456 => false, _ => false }"]
fn test_match_expr(x: i32) -> i32 {
    assert!(x == -42);
    x * 2
}

fn main() {

}
