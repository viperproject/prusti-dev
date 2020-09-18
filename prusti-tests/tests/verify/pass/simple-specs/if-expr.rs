//! Example: test if expressions

use prusti_contracts::*;

fn rand() -> bool { true }

#[requires(x == 42)]
#[ensures(if result > 0 { result == 42 } else { result == 0 })]
fn test_if_expr(x: u32) -> u32 {
    assert!(x == 42);
    if rand() {
        x
    } else {
        0
    }
}

fn main() {

}
