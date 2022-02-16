// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"

use prusti_contracts::*;

#[assert_on_expiry(true, a)]
fn test1(a: bool) {}

#[assert_on_expiry(result => true, a)]
fn test2(a: bool) {}

#[assert_on_expiry(
    true, 
    result == match x {
        1 => 1,
        2 => 2,
        _ => 0,
    }
)]
fn test3(x: u32) -> u32 {
    1
}

fn main() {}

