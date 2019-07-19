extern crate prusti_contracts;

#[pure]
#[requires="std::i32::MIN <= a && a <= std::i32::MAX"]
#[requires="std::i32::MIN <= b && b <= std::i32::MAX"]
fn safe_mult_i32(a: i32, b: i32) -> bool {
    let res = (a as i64) * (b as i64);
    (std::i32::MIN as i64) <= res && res <= (std::i32::MAX as i64)
}

#[pure]
#[requires="std::i32::MIN <= a && a <= std::i32::MAX"]
#[requires="std::i32::MIN <= b && b <= std::i32::MAX"]
fn safe_add_i32(a: i32, b: i32) -> bool {
    let res = (a as i64) + (b as i64);
    (std::i32::MIN as i64) <= res && res <= (std::i32::MAX as i64)
}

#[requires="safe_mult_i32(*s, a)"]
fn mul_assign(s: &mut i32, a: i32) {
    assert!(safe_mult_i32(*s, a));
    assert!(-2147483648 <= (*s as i64) * (a as i64));
    assert!((*s as i64) <= 2147483647);
    assert!((a as i64) <= 2147483647);
    assert!((*s as i64) * (a as i64) <= 2147483647);
    *s = *s * a
}

#[requires="safe_add_i32(*s, a)"]
fn add_assign(s: &mut i32, a: i32) {
    *s = *s + a
}

#[trusted]
#[requires="safe_mult_i32(*s, a) && safe_add_i32(*s * a, b)"]
fn mul_add_assign(s: &mut i32, a: i32, b: i32) {
    *s = (*s * a) + b
}

fn main() {}
