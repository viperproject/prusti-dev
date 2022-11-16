// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"
// normalize-stdout-test: "#\[prusti::specs_version = \x22.+\x22\]" -> "#[prusti::specs_version = $(SPECS_VERSION)]"

use prusti_contracts::*;

#[requires(true)]
fn test1() {}

#[ensures(true)]
fn test2() {}

fn test3() {
    for _ in 0..2 {
        body_invariant!(true)
    }
}

#[requires(true)]
#[ensures(true)]
fn test4() {
    for _ in 0..2 {
        body_invariant!(true)
    }
}

fn main() {}
