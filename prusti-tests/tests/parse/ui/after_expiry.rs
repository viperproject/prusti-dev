// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"
// normalize-stdout-test: "#\[prusti::specs_version = \x22.+\x22\]" -> "#[prusti::specs_version = $(SPECS_VERSION)]"

use prusti_contracts::*;

#[after_expiry(a)]
fn test1(a: bool) {}

#[after_expiry(result => a)]
fn test2(a: bool) {}

#[after_expiry(
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
