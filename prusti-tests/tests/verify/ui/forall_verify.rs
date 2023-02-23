// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"
// normalize-stdout-test: "#\[prusti::specs_version = \x22.+\x22\]" -> "#[prusti::specs_version = $(SPECS_VERSION)]"

use prusti_contracts::*;

#[pure]
fn identity(x: i32) -> i32 { x }

#[ensures(forall(|x: i32| true))]
fn test1() {}

#[ensures(forall(|x: i32| identity(x) == x))]
fn test2() {}

#[ensures(forall(|x: i32| identity(x) == x + 1))]
fn test3() {}

#[ensures(exists(|x: i32| true))]
fn test4() {}

#[ensures(identity(1) == 1)]     // A witness.
#[ensures(exists(|x: i32| identity(x) == x))]
fn test5() {}

#[ensures(exists(|x: i32| identity(x) == x + 1))]
fn test6() {}

fn main() {}
