//@rustc-env: PRUSTI_QUIET=true
use prusti_contracts::*;

predicate! {
    //#[insert_runtime_check] -> this would fix it
    fn some_pred(x: i32) -> bool {
        x == 42
    }
}

// for predicates to be used in specifications that are checked at runtime, they need
// to be marked with #[insert_runtime_check] too, which is not the case here
#[insert_runtime_check]
#[requires(some_pred(_x))] //~ ERROR: Referring to predicate that is not runtime checkable
fn foo(_x: i32) {}

#[trusted]
fn bar(x: i32) {
    // same problem here
    prusti_assert!(#[insert_runtime_check]some_pred(x))
    //~^ ERROR: Referring to predicate that is not runtime checkable
}

fn main() {
    bar(42);
    foo(42);
}
