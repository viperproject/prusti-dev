extern crate prusti_contracts;

struct T {
    f: u32,
}

struct U {
    f: u32,
    g: u32,
}

#[requires="_a.f == 4"]
fn check_t(_a: T) {}

#[requires="_a.f == 3 && _a.g == 4"]
fn check_u(_a: U) {}

#[ensures="*result == old(*x)"]
#[ensures="after_expiry(before_expiry(*result) == *x)"]
fn reborrow_u32(x: &mut u32) -> &mut u32 {
    x
}

fn borrow_u32(_x: &mut u32) {
}

pub fn test1() {
    let mut a = 6;
    let x = reborrow_u32(&mut a);
    assert!(*x == 6);
    *x = 4;
    assert!(a == 4);
}

pub fn test2() {
    let mut a = 6;
    borrow_u32(&mut a);
}

fn main() {}
