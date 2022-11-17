// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"
// normalize-stdout-test: "#\[prusti::specs_version = \x22.+\x22\]" -> "#[prusti::specs_version = $(SPECS_VERSION)]"

/// Failure case for predicate parsing: can only be used on function definitions

use prusti_contracts::*;

// doesn't work on just function decl
predicate! {
    fn result_is_one() -> bool;
}

// doesn't work on non-function-y items
predicate! {
    static FOO: usize = 0;
}


// incompatible with other prusti attributes
predicate! {
    #[pure]
    fn something() -> bool {
        true
    }
}

// parsing is different depending on the 'outermost' predicate, so a test the other way around
// makes sense as well
predicate! {
    #[trusted]
    fn other_thing() -> bool {
        false
    }
}

fn main() {}
