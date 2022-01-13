// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"

use prusti_contracts::*;

#[requires(exists)]
fn test1() {}

#[requires(exists())]
fn test2() {}

#[requires(exists(|))]
fn test3() {}

#[requires(exists(||) 1+1)]
fn test4() {}

#[requires(exists(|a, b| true))]
fn test5() {}

#[requires(exists(||) || exists(||))]
fn test6() {}

#[requires(exists(|| 1+1 == 1+1, triggers=[(1,)]))]
fn test7() {}

#[requires(exists(|| true, triggers=[(1,2), (1,)]))]
fn test8() {}

#[requires(exists(|| true, triggers=1))]
fn test9() {}

#[requires(exists(||))]
fn test10() {}

#[requires(exists(|| 1+1 == 1+1))]
fn test11() {}

#[requires(exists(||, triggers=[]))]
fn test12() {}

#[requires(exists(|| 1+1 == 1+1, triggers=[(1,)]))]
fn test13() {}

#[requires(exists(|a: i32| true, triggers=[1]))]
fn test14() {}

#[requires(exists(|a: i32| true, triggers=[(1, 2), 1,]))]
fn test15() {}

fn main() {}
