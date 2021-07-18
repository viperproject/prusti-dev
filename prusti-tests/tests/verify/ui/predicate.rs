// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"
// normalize-stdout-test: "\[[a-z0-9]{4}\]::" -> "[$(CRATE_ID)]::"


use prusti_contracts::*;

#[pure]
fn identity(x: i32) -> i32 { x }

predicate! {
    fn true_p1() -> bool {
        forall(|x: i32| true)
    }
}

predicate! {
    fn true_p2() -> bool {
        exists(|x: i32| true)
    }
}

predicate! {
    fn forall_identity() -> bool {
        forall(|x: i32| identity(x) == x)
    }
}

predicate! {
    fn exists_identity() -> bool {
        exists(|x: i32| identity(x) == x, triggers=[(identity(x),),])
    }
}

#[requires(true_p1())]
#[requires(forall_identity())]
fn test_identity_1() {}

#[requires(true_p2())]
#[requires(exists_identity())]
fn test_identity_2() {}

predicate! {
    fn false_p() -> bool {
        false
    }
}

// this must pass, i.e. the evaluation must not short-circuit if a predicate
// somewhere down the call stack is false
#[requires(false_p() || true)]
fn precond_or_correctly() -> bool {
    true
}

fn main() {
    // Provide an existential witness.
    assert!(identity(5) == 5);
    test_identity_1();
    test_identity_2();
    precond_or_correctly();
}
