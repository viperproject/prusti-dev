// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_qi_bound_global=10000 -Psmt_qi_bound_trace=200 -Psmt_qi_bound_trace_kind=20 -Psmt_qi_bound_global_kind=100

use prusti_contracts::*;

#[requires(a == 4)]
#[ensures(old(a) == 4)]
fn test1(a: i32) {}

#[requires(a == 4)]
#[ensures(old(a) == 5)] //~ ERROR postcondition might not hold.
fn test2(a: i32) {}

#[requires(a == 4)]
#[ensures(old(a) == 4)]
fn test3(mut a: i32) {
    a = 5;
}

#[requires(a == 4)]
#[ensures(old(a) == 5)] //~ ERROR postcondition might not hold.
fn test4(mut a: i32) {
    a = 5;
}

#[requires(a == 4)]
#[ensures(a == 4)]
fn test5(mut a: i32) {
    a = 5;
}

#[requires(a == 4)]
#[ensures(a == 5)] //~ ERROR postcondition might not hold.
fn test6(mut a: i32) {
    a = 5;
}

fn test7() {
    test5(4);
    assert!(false); //~ ERROR the asserted expression might not hold
}

#[requires(a < 10)]
#[ensures(result == old(a) + 1)]
fn inc1(a: i32) -> i32 {
    a + 1
}

fn test8() {
    let a = 5;
    let b = inc1(a);
    assert!(b == 6);
}

fn test9() {
    let a = 5;
    let b = inc1(a);
    assert!(b == 6);
    assert!(false); //~ ERROR the asserted expression might not hold
}

#[requires(a < 10)]
#[ensures(result == old(a) + 1)]
fn inc2(mut a: i32) -> i32 {
    a += 1;
    a
}

fn test10() {
    let a = 5;
    let b = inc2(a);
    assert!(b == 6);
}

fn test11() {
    let a = 5;
    let b = inc2(a);
    assert!(b == 6);
    assert!(false); //~ ERROR the asserted expression might not hold
}

#[requires(a < 10)]
#[ensures(result == a + 1)]
fn inc3(mut a: i32) -> i32 {
    a + 1
}

fn test12() {
    let a = 5;
    let b = inc3(a);
    assert!(b == 6);
}

fn test13() {
    let a = 5;
    let b = inc3(a);
    assert!(b == 6);
    assert!(false); //~ ERROR the asserted expression might not hold
}

#[requires(a == 4)]
#[ensures(old(a) != 4)] //~ ERROR
fn test14(mut a: i32) {
    a = 5;
}

fn main() {}
