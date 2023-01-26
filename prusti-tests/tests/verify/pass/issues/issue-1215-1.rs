use prusti_contracts::*;

fn main() {}

// #[requires(0 <= i)] // This should not be needed, if encode_unsigned_num_constraint=true is the default
#[requires(i < s.len())]
fn _test(s: &[i64], i: usize) -> i64 {
    s[i]
}