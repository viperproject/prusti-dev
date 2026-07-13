// Coverage for `bool as <integer>` casts. Rust's `bool` is now represented by
// Viper's native `Bool`, and `b as iN`/`b as uN` encodes as `b ? 1 : 0`.

use prusti_contracts::*;

#[ensures(b ==> result == 1)]
#[ensures(!b ==> result == 0)]
fn to_i32(b: bool) -> i32 {
    b as i32
}

#[ensures(b ==> result == 1)]
#[ensures(!b ==> result == 0)]
fn to_u8(b: bool) -> u8 {
    b as u8
}

// The source of the cast may be a comparison result.
#[ensures(result == if x < y { 1 } else { 0 })]
fn lt_as_usize(x: i32, y: i32) -> usize {
    (x < y) as usize
}

fn constants() {
    assert!(true as i32 == 1);
    assert!(false as u64 == 0);
    assert!((3 > 2) as i8 == 1);
    assert!((2 > 3) as u32 == 0);
}

fn use_fns() {
    assert!(to_i32(true) == 1);
    assert!(to_u8(false) == 0);
    assert!(lt_as_usize(1, 2) == 1);
    assert!(lt_as_usize(2, 1) == 0);
}
