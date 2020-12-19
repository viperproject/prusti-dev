// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

use prusti_contracts::*;

#[requires(true && true || true)]
fn test1() {}

#[requires(forall(|a: i32| a == 5) || forall(|a: i32| a == 5))]
fn test2() {}

fn main() {}
