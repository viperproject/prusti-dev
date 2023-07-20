// compile-flags: -Pencode_bitvectors=true

use prusti_contracts::*;

fn shift_left_1() {
    let a = 1u8;
    let b = a << 2u32;
    assert!(b == 4);
}

fn shift_left_2() {
    let a = 1u8;
    let b = a << 2u32;
    assert!(b == 8);    //~ ERROR: the asserted expression might not hold
}

fn shift_left_3() {
    let a = 1u8;
    let _b = a << 8u32;    //~ ERROR: assertion might fail with "attempt to shift left with overflow"
                        //~^ ERROR: this arithmetic operation will overflow
}

fn shift_unsigned_right_1() {
    let a = 4u8;
    let b = a >> 2u32;
    assert!(b == 1);
}

fn shift_unsigned_right_2() {
    let a = 4u8;
    let b = a >> 2u32;
    assert!(b == 2);    //~ ERROR: the asserted expression might not hold
}

fn shift_unsigned_right_3() {
    let a = 4u8;
    let b = a >> 9u32;     //~ ERROR: assertion might fail with "attempt to shift right with overflow"
                        //~^ ERROR: this arithmetic operation will overflow
}

fn shift_unsigned_right_4() {
    let a = 255u8;
    let b = a >> 2u32;
    assert!(b == 63);
}

fn shift_signed_right_1() {
    let a = -1i8;
    let b = a >> 2u32;
    assert!(b == -1);
}

fn shift_signed_right_2() {
    let a = -1i8;
    let b = a >> 2u32;
    assert!(b == -2);   //~ ERROR: the asserted expression might not hold
}

fn shift_signed_right_3() {
    let a = -1i8;
    let b = a >> 9u32;     //~ ERROR: assertion might fail with "attempt to shift right with overflow"
                        //~^ ERROR: this arithmetic operation will overflow
}

fn shift_signed_right_4() {
    let a = 4i8;
    let b = a >> 2u32;
    assert!(b == 1);
}

fn main() {}
