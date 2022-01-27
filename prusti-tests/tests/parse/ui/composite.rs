// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"

use prusti_contracts::*;

#[requires(true && true ==> true && true)]
fn test1() {}

#[requires(true && (true ==> true) && (true || true) && true)]
fn test2() {}

#[requires((true && true) ==> true)]
fn test3() {}

#[requires((true ==> true) && true ==> true)]
fn test4() {}

#[requires((true ==> true) && (true ==> true && (true || true)))]
fn test5() {}

#[requires((true && true) ==> true ==> true ==> true ==> true)]
fn test6() {}

#[requires((true && true) ==> (true && true) ==> (true && true))]
fn test7() {}

#[requires((true || true) ==> (true || true))]
fn test8() {}

#[requires((true || true) ==> (true || (true && (true || true))))]
fn test9() {}

#[requires(true && forall(|a: i32| a == 5))]
fn test10() {}

#[requires(forall(|a: i32| a == 5))]
fn test12() {}

#[requires(true ==> forall(|a: i32, b: i32| a == 5) ==> true)]
fn test13() {}

#[requires(true ==> forall(|a: i32| a == 5))]
fn test14() {}

#[requires(forall(|a: i32| a == 5) ==> true)]
fn test15() {}

#[requires(forall(|b: i32| b == 10) ==> true ==> forall(|a: u32, b: u32| a == 5))]
fn test16() {}

#[requires(true && exists(|a: i32| a == 5))]
fn test17() {}

#[requires(exists(|a: i32| a == 5))]
fn test19() {}

#[requires(true ==> exists(|a: i32, b: i32| a == 5) ==> true)]
fn test20() {}

#[requires(true ==> exists(|a: i32| a == 5))]
fn test21() {}

#[requires(exists(|a: i32| a == 5) ==> true)]
fn test22() {}

#[requires(exists(|b: i32| b == 10) ==> true ==> exists(|a: u32, b: u32| a == 5))]
fn test23() {}

#[requires(true && true || true)]
fn test24() {}

#[requires(forall(|a: i32| a == 5) || forall(|a: i32| a == 5))]
fn test25() {}

#[requires(exists(|a: i32| a == 5) || exists(|a: i32| a == 5))]
fn test26() {}

fn main() {}
