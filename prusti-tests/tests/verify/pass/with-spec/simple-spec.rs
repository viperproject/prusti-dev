//! Example: test simple specifications without old expressions

use prusti_contracts::*;

#[requires(x == 42)]
#[ensures(result == 42)]
fn test_unsigned_int(x: u32) -> u32 {
    assert!(x == 42);
    x
}

#[requires(x == -42)]
#[ensures(result == -42)]
fn test_signed_int(x: i32) -> i32 {
    assert!(x == -42);
    x
}

#[requires(x)]
#[ensures(result == true)]
fn test_bool(x: bool) -> bool {
    assert!(x);
    x
}

fn main() {

}
