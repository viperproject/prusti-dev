//! Example: test match expressions

// ignore-test TODO

extern crate prusti_contracts;

#[requires="x == -42"]
#[ensures="match result { Some(_) => true, None => false }"]
fn test_match_expr(x: i32) -> Option<i32> {
    assert!(x == -42);
    Some(x)
}

fn main() {

}
