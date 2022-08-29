// compile-flags: -Pprint_desugared_specs=true -Pprint_collected_verification_items=true -Phide_uuids=true
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
    let mut curr = 0;
    while curr < 2 {
        body_invariant!(true);
        curr += 1;
    }
}

#[requires(true)]
#[ensures(true)]
fn test4() {
    let mut curr = 0;
    while curr < 2 {
        body_invariant!(true);
        curr += 1;
    }
}

fn main() {}
