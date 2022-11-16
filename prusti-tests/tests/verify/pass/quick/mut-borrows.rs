use prusti_contracts::*;

struct T {
    f: u32,
}

struct U {
    f: u32,
    g: u32,
}

#[requires(_a.f == 4)]
fn check_t(_a: T) {}

#[requires(_a.f == 3 && _a.g == 4)]
fn check_u(_a: U) {}

pub fn test1() {
    let mut a = 6;
    let x = &mut a;
    *x = 4;
    assert!(a == 4);
}

pub fn test2() {
    let mut a = 6;
    let x = &mut a;
    let y = &mut *x;
    let z = &mut *y;
    *z = 4;
    assert!(a == 4);
}

pub fn test3() {
    let mut a = T { f: 6};
    let x = &mut a;
    x.f = 4;
    assert!(a.f == 4);
    check_t(a);
}

pub fn test4() {
    let mut a = T { f: 6 };
    let x = &mut a;
    let y = &mut x.f;
    let z = &mut *y;
    *z = 4;
    assert!(a.f == 4);
    check_t(a);
}

pub fn test5() {
    let mut a = U { f: 6, g: 1, };
    let x = &mut a;
    let y = &mut x.f;
    let z = &mut x.g;
    *y = 7;
    let y2 = &mut *y;
    let z2 = &mut *z;
    *y2 = 3;
    *z2 = 4;
    assert!(a.f == 3);
    assert!(a.g == 4);
    check_u(a);
}

pub fn test6() {
    let mut a = U { f: 6, g: 1, };
    let y = &mut a.f;
    let z = &mut a.g;
    *y = 7;
    let y2 = &mut *y;
    let z2 = &mut *z;
    *y2 = 3;
    *z2 = 4;
    assert!(a.f == 3);
    assert!(a.g == 4);
    check_u(a);
}

fn main() {}
