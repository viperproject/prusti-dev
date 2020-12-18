// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pskip_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

use prusti_contracts::*;

#[requires(forall(|a: i32, b: u32| a == a, triggers=[(a==a, a==a), (true,)]))]
fn test1() {}

fn main() {}
