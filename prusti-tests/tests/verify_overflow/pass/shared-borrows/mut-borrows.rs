use prusti_contracts::*;

fn borrow(_x: &u32) {}

pub fn test1(mut a: u32) {
    let x = &mut a;
    let _y = &*x;
}

pub fn test2(x: &mut u32) {
    let _y = &*x;
}

pub fn test3(x: &mut u32) {
    let y = &*x;
    assert!(*y == *x);
    let _a = *y;
}

#[ensures(*x == 5)]
pub fn test4(x: &mut u32) {
    let y = &*x;
    assert!(*y == *x);
    let a = *y;
    assert!(a == *y && a == *x);
    *x = 5;
}

fn main() {
}
