// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=100

use prusti_contracts::*;

fn test1() {
    let mut a = 1;
    let _b = &mut a;
    a = 3;
}

fn test2() {
    let mut a = 1;
    let _b = &mut a;
    a = 3;
    assert!(false);    //~ ERROR: the asserted expression might not hold
}

fn test3() {
    let mut a = 1;
    let mut b = &mut a;
    let c = &mut b;
    a = 3;
}

fn test4() {
    let mut a = 1;
    let mut b = &mut a;
    let c = &mut b;
    a = 3;
    assert!(false);    //~ ERROR: the asserted expression might not hold
}

fn test5() {
    let mut a = [[1; 10]; 20];
    let mut b = &mut a;
    let c = &mut b;
    a[2][1] = 3;
}

fn test6() {
    let mut a = [[1; 10]; 20];
    let mut b = &mut a;
    let c = &mut b;
    a[2][1] = 3;
    assert!(a[2][1] == 4);    //~ ERROR: the asserted expression might not hold
}

fn test7() {
    let mut a = 1;
    let b = &mut a;
    assert!(*b == 1);
    assert!(a == 1);
}

fn test8() {
    let mut a = 1;
    let b = &mut a;
    assert!(*b == 1);
    assert!(a == 2);    //~ ERROR: the asserted expression might not hold
}

fn test9() {
    let mut a = 1;
    let b = &mut a;
    *b = 2;
    assert!(a == 2);
}

fn test10() {
    let mut a = 1;
    let b = &mut a;
    *b = 2;
    assert!(a == 1);    //~ ERROR: the asserted expression might not hold
}

fn test11() {
    let a = 1;
    let b = &a;
    let c = *b;
    assert!(c == 1);
    assert!(a == 1);
}

fn test12() {
    let mut a = 1;
    let b = &mut a;
    let c = *b;
    assert!(c == 1);
    assert!(a == 1);
}

struct T {
    value: i32,
}

struct U {
    f: T,
    g: T,
}

fn test13(mut a: U) {
    let b = a.g.value;
    let x = &mut a;
    x.f.value = 4;
    // FIXME: This should work.
    assert!(a.f.value == 4);    //~ ERROR: the asserted expression might not hold
    //assert!(b == a.g.value);  FIXME
}

fn test14(mut a: U) {
    let x = &mut a;
    assert!(x.f.value == 4);    //~ ERROR: the asserted expression might not hold
}

fn test15(mut a: U) {
    let x = &mut a.f;
    x.value = 4;
    // FIXME: This should work.
    assert!(a.f.value == 4);    //~ ERROR: the asserted expression might not hold
}

fn test16(mut a: U) {
    let x = &mut a.f;
    assert!(x.value == 4);    //~ ERROR: the asserted expression might not hold
}

fn test17(a: U) {
    let x = &a;
    let b = x.f.value;
    assert!(b == a.f.value);
}

fn test18(mut a: U) {
    let x = &mut a.f;
    let b = x.value;
    // FIXME: This should work.
    assert!(b == a.f.value);    //~ ERROR: the asserted expression might not hold
}

fn test19(a: U) {
    let x = &a;
    let b = x.f.value;
    assert!(b == 2);    //~ ERROR: the asserted expression might not hold
}

fn test20(mut a: U) {
    let x = &mut a.f;
    let b = x.value;
    assert!(b == 2);    //~ ERROR: the asserted expression might not hold
}

struct T2 {
    f: i32,
    g: i32,
}

fn test21(x: &mut T2, a: i32) -> bool{
    x.f = 1;
    x.g = 1;
    x.f = 2;
    x.f = a;
    x.f > 0
}

#[ensures(result)]
fn test22(x: &mut T2, a: i32) -> bool { //~ ERROR: postcondition might not hold.
    x.f = 1;
    x.g = 1;
    x.f = 2;
    x.f = a;
    x.f > 0
}

fn test23(x: &mut [i32]) {
    x[0] = 4;  //~ ERROR: the array or slice index may be out of bounds
}

fn main() {}
