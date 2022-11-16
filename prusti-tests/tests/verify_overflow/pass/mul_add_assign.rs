/// Source: num_traits::ops[0]::mul_add[0]::{{impl}}[*]::mul_add_assign[0]

use prusti_contracts::*;

#[requires(-1000 < *s && *s < 1000)]
//#[requires(-1000 < a && a < 1000)]   // Non-linear arithmetic makes the test unstable.
#[requires(a == 1000)]
#[requires(-1000 < b && b < 1000)]
fn mul_add_assign(s: &mut i32, a: i32, b: i32) {
    *s = (*s * a) + b
}

fn main() {}
