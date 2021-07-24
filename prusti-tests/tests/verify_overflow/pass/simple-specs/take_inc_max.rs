use prusti_contracts::*;

/// Example 1 / Figure 1 from the paper "RustHorn: CHC-based Verification for Rust Programs"
/// authored by Yusuke Matsushita, Takeshi Tsukada, and Naoki Kobayashi

#[ensures(*result >= old(*ma) && *result >= old(*mb))]
#[ensures(*result == old(*ma) || *result == old(*mb))]
#[after_expiry(if old(*ma >= *mb) {
        (*ma == before_expiry(*result) && *mb == old(*mb))
    } else {
        (*ma == old(*ma) && *mb == before_expiry(*result))
    })]
fn take_max<'a>(ma: &'a mut i32, mb: &'a mut i32) -> &'a mut i32 {
    if *ma >= *mb { ma } else { mb }
}

#[requires(a < i32::MAX)]
#[requires(b < i32::MAX)]
#[ensures(result == true)]
fn inc_max(mut a: i32, mut b: i32) -> bool {
    // Optional, to avoid the warning on the mutable arguments
    // let mut a = a;
    // let mut b = b;
    {
        let mc = take_max(&mut a, &mut b);
        *mc += 1;
    }
    a != b
}

fn main() {}
