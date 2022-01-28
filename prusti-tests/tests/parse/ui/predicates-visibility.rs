// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"

/// Tests for predicate visibility

use prusti_contracts::*;

mod foo {
    use super::{predicate, forall};
    predicate! {
        pub fn pred1(a: bool) -> bool {
            forall(|b: bool| a == b)
        }
    }
}

#[requires(foo::pred1(true))]
fn test_pub_pred() {}

fn main() {}
