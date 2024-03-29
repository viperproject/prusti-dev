// ignore-test

// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"
// normalize-stdout-test: "#\[prusti::specs_version = \x22.+\x22\]" -> "#[prusti::specs_version = $(SPECS_VERSION)]"

/// Failure case for closure macro parsing: missing argument type.

use prusti_contracts::*;

fn main() {
    // TODO: the error is reported with an indicator next to `i` below, but the
    // error is not very clear overall.
    let f = closure!(
        #[requires(i >= 0)]
        #[ensures(result == i + 1)]
        |i| -> i32 { i + 1 }
    );
}
