extern crate prusti_contracts;

#[repr(C)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

use prusti_contracts::*;

#[extern_spec(
    {file = "prusti-tests/tests/verify/pass/verifast/functions.c",}
    crate)]
extern "C" {
    #[ensures({translator = "verifast"}result == a + b)]
    pub fn add(a: i32, b: i32) -> i32;

    #[ensures({translator = "verifast"}p.x == old(p.y))]
    #[ensures({translator = "verifast"}p.y == old(p.x))]
    pub fn swap(p: &mut Point);

    #[ensures({translator = "verifast"}
        p.x == old(p.y + p.x) && p.y == old(p.y - p.x))]
    #[ensures({translator = "verifast"}result == p.x * p.y)]
    pub fn mangle(p: &mut Point) -> i32;

    #[ensures({translator = "verifast"}result == p.x * p.x + p.y * p.y)]
    pub fn squared_magnitude(p: &Point) -> i32;
}

extern "C" {
    pub fn add(a: i32, b: i32) -> i32;
    
    pub fn swap(p: &mut Point);

    pub fn mangle(p: &mut Point) -> i32;

    pub fn squared_magnitude(p: &Point) -> i32;
}

fn main() {
    use prusti_contracts::*;

    let a = 3;
    let b = 4;
    let r = unsafe { add(a, b) };
    prusti_assert_eq!(r, a + b);

    let x_val = 11;
    let y_val = 5;
    let mut p = Point { x: x_val, y: y_val };
    unsafe { swap(&mut p);}
    prusti_assert_eq!(p.x, y_val);
    prusti_assert_eq!(p.y, x_val);

    let new_x_val = x_val + y_val;
    let new_y_val = x_val - y_val;
    let r_val = new_x_val * new_y_val;
    
    let r = unsafe { mangle(&mut p) };
    
    prusti_assert_eq!(r, r_val);
    prusti_assert_eq!(p.x, new_x_val);
    prusti_assert_eq!(p.y, new_y_val);

    let p = Point { x: a, y: b };
    let r = unsafe { squared_magnitude(&p) };
    prusti_assert_eq!(r, a*a + b*b);
    prusti_assert_eq!(p.x, a);
    prusti_assert_eq!(p.y, b);
}
