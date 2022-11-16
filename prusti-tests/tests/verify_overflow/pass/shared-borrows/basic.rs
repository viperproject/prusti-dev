use prusti_contracts::*;

pub fn test1() {
    let a = 4;
    let _x = &a;
}

pub fn test2(a: u32) {
    let _x = &a;
}

pub fn test3() {
    let mut a = 5;
    let x = &a;
    let y = &a;
    let _b = *x;
    let _c = *y;
    a = 6;
    let _b = a;
}

/*
pub fn test3() {
    TODO: Implement without killing for now because we have not seen
    anyone to write code like this in practice.
    let mut a = 5;
    let mut b = 5;
    let mut x = &mut a;
    let y = &*x;
    let z = &*x;
    x = &mut b;
    let c = *y;
    let d = *z;
    *x = 6;
    assert!(b == 6);
    assert!(a == 5 && c == 5 && d == 5);
}
*/

pub fn test4(a: u32) {
    let x = &a;
    let y = &a;
    let _b = *x;
    let _c = *y;
}

pub fn test5() {
    let mut a = 5;
    let x = &a;
    let y = x;
    let _b = *x;
    let _c = *y;
    a = 6;
    let _b = a;
}

fn main() {
}
