use prusti_contracts::*;

// `as` casts between integers never panic: the value is preserved when it fits
// in the target, and otherwise truncated to the target width and reinterpreted
// with the target's signedness. These assertions pin that behaviour; they hold
// even with overflow checks enabled, since an `as` cast never overflows.

fn widening_preserves() {
    assert!(200u8 as u16 == 200u16);
    assert!(1234u16 as u64 == 1234u64);
    assert!(-5i8 as i32 == -5i32);
    assert!(5i8 as u32 == 5u32);
}

fn narrowing_truncates() {
    assert!(256u64 as u8 == 0);
    assert!(257u64 as u8 == 1);
    assert!(300i32 as u8 == 44);
    assert!(65536u32 as u16 == 0);
}

fn sign_reinterpret() {
    assert!(255u8 as i8 == -1);
    assert!(128u8 as i8 == -128);
    assert!(-1i8 as u8 == 255);
    assert!(-5i8 as u8 == 251);
}

fn preserve_sign() {
    assert!(5u8 as i128 == 5i128);
    assert!(5u16 as i128 == 5i128);
    assert!(5u32 as i128 == 5i128);
    assert!(5u64 as i128 == 5i128);

    assert!(5u8 as u128 == 5u128);
    assert!(5u16 as u128 == 5u128);
    assert!(5u32 as u128 == 5u128);
    assert!(5u64 as u128 == 5u128);
    assert!(5i128 as u128 == 5u128);

    assert!(5i8 as i128 == 5i128);
    assert!(5i16 as i128 == 5i128);
    assert!(5i32 as i128 == 5i128);
    assert!(5i64 as i128 == 5i128);
    assert!(5i128 as i128 == 5i128);

    assert!(-5i8 as i128 == -5i128);
    assert!(-5i16 as i128 == -5i128);
    assert!(-5i32 as i128 == -5i128);
    assert!(-5i64 as i128 == -5i128);
    assert!(-5i128 as i128 == -5i128);
}

// Boundary values via `::MAX`/`::MIN`. The 128-bit cases exercise the full-width
// modulo (`get_modulo_int`): a small-value cast can't detect a wrong modulus,
// but wrapping `MAX`/`MIN` at the full width does.
fn max_min_wrap() {
    // signed `-1` wraps to the unsigned `MAX`
    assert!(-1i8 as u8 == u8::MAX);
    assert!(-1i16 as u16 == u16::MAX);
    assert!(-1i32 as u32 == u32::MAX);
    assert!(-1i64 as u64 == u64::MAX);
    assert!(-1i128 as u128 == u128::MAX);
    // widening a negative signed value to a wider unsigned type still wraps to MAX
    assert!(-1i8 as u128 == u128::MAX);
    assert!(-1i64 as u128 == u128::MAX);

    // unsigned `MAX` reinterpreted at the same width is `-1`
    assert!(u8::MAX as i8 == -1);
    assert!(u64::MAX as i64 == -1);
    assert!(u128::MAX as i128 == -1);

    // narrowing an all-ones `MAX` keeps the low bits (target `MAX` / `-1`)
    assert!(u128::MAX as u8 == u8::MAX);
    assert!(u64::MAX as u32 == u32::MAX);
    assert!(i128::MAX as u8 == u8::MAX);
    assert!(i128::MAX as i8 == -1);

    // signed `MIN`
    assert!(i8::MIN as u8 == 128);
    assert!(i128::MIN as i8 == 0);
    assert!(i128::MIN as u8 == 0);
    assert!(i64::MIN as i8 == 0);
}
