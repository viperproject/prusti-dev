use prusti_contracts::*;

#[requires(a as f32 as i32 == 0)]
fn unsupported_cast(a: i64) {}

fn main() {}
