// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pno_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"

/// Tests for predicate parsing and desugaring

use prusti_contracts::*;

predicate! {
    fn pred1(a: bool) -> bool {
        forall(|b: bool| a == b)
    }
}

#[requires(pred1(true))]
fn use_pred1() {}

predicate! {
    fn pred2(a: bool) -> bool {
        exists(|b: bool| a == b)
    }
}

#[requires(pred2(true))]
fn use_pred2() {}

predicate! {
    fn forall_implication() -> bool {
        forall(|x: usize| (x != 0) ==> x*2 != 0)
    }
}

predicate! {
    fn exists_implication() -> bool {
        exists(|x: usize| (x != 0) ==> x*2 != 0)
    }
}

fn main() {}
