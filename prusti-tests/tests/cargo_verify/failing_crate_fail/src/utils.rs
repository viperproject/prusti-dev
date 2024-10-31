use prusti_contracts::*;

#[requires(x > 999)]
pub fn requires_large_number(x: i32) -> i32 {
    x
}
