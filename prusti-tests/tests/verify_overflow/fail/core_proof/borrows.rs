// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=100

use prusti_contracts::*;

fn test1() {
    let mut a = 1;
    let _b = &mut a;
    a = 3;
}

fn test2() {
    let mut a = 1;
    let b = &mut a;
    assert!(*b == 1);
    assert!(a == 1);
}

fn test2_1() {
    let mut a = 1;
    let b = &mut a;
    assert!(*b == 1);
    assert!(a == 2);    //~ ERROR: the asserted expression might not hold
}

fn test3() {
    let mut a = 1;
    let b = &mut a;
    *b = 2;
    assert!(a == 2);
}

fn test4() {
    let mut a = 1;
    let b = &mut a;
    *b = 2;
    assert!(a == 1);    //~ ERROR: the asserted expression might not hold
}

fn test5() {
    let a = 1;
    let b = &a;
    let c = *b;
    assert!(c == 1);
    assert!(a == 1);
}

fn test6() {
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

fn test7(mut a: U) {
    let b = a.g.value;
    let x = &mut a;
    x.f.value = 4;
    assert!(a.f.value == 4);
    assert!(b == a.g.value);
}

fn test8(mut a: U) {
    let x = &mut a;
    assert!(x.f.value == 4);    //~ ERROR: the asserted expression might not hold
}

fn test9(mut a: U) {
    let x = &mut a.f;
    x.value = 4;
    assert!(a.f.value == 4);
}

fn test10(mut a: U) {
    let x = &mut a.f;
    assert!(x.value == 4);    //~ ERROR: the asserted expression might not hold
}

fn test11(a: U) {
    let x = &a;
    let b = x.f.value;
    assert!(b == a.f.value);
}

fn test12(mut a: U) {
    let x = &mut a.f;
    let b = x.value;
    assert!(b == a.f.value);
}

fn test13(a: U) {
    let x = &a;
    let b = x.f.value;
    assert!(b == 2);    //~ ERROR: the asserted expression might not hold
}

fn test14(mut a: U) {
    let x = &mut a.f;
    let b = x.value;
    assert!(b == 2);    //~ ERROR: the asserted expression might not hold
}

struct T2 {
    f: i32,
    g: i32,
}

fn test15(x: &mut T2, a: i32) -> bool{
    x.f = 1;
    x.g = 1;
    x.f = 2;
    x.f = a;
    x.f > 0
}

#[ensures(result)]
fn test16(x: &mut T2, a: i32) -> bool { //~ ERROR: postcondition might not hold.
    x.f = 1;
    x.g = 1;
    x.f = 2;
    x.f = a;
    x.f > 0
}

fn main() {}
