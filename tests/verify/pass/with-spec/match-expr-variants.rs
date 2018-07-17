//! Example: test match expressions

// ignore-test We need to extract the discriminant of each variant

extern crate prusti_contracts;

#[requires="x == -42"]
#[ensures="match result { Some(..) => true, _ => false }"]
fn test_match_expr(x: i32) -> Option<i32> {
    assert!(x == -42);
    Some(x)
}

fn main() {

}
